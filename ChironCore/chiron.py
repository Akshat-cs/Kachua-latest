#!/usr/bin/env python3
Release = "Chiron v1.0.4"

import ast
import sys
from ChironAST.builder import astGenPass
import abstractInterpretation as AI
import dataFlowAnalysis as DFA
from sbfl import testsuiteGenerator
import ChironAST.ChironAST as ChironAST

sys.path.insert(0, "../Submission/")
sys.path.insert(0, "ChironAST/")
sys.path.insert(0, "cfg/")

import pickle
import time
import turtle
import argparse
from interpreter import *
from irhandler import *
from fuzzer import *
import sExecution as se
import cfg.cfgBuilder as cfgB
import submissionDFA as DFASub
import submissionAI as AISub
from sbflSubmission import computeRanks
import csv
# Adding SSA conversion imports
from SSAConverter import SSAConverter
from SSADestroyer import SSADestroyer
# Adding Dead Code Elimination Imports
from DeadCodeElimination import DeadCodeElimination

def cleanup():
    pass

def stopTurtle():
    turtle.bye()

def cfg_to_ir(cfg):
    """
    Enhanced CFG to IR conversion that properly preserves control flow.
    
    This implementation:
    1. Collects all basic blocks in a deterministic order
    2. Preserves the connections between blocks 
    3. Correctly calculates jump offsets for conditional branches
    4. Handles backward jumps for loops
    
    Args:
        cfg: A ChironCFG instance
    
    Returns:
        A list of (instruction, jump_offset) tuples
    """
    print("Converting CFG to IR with enhanced control flow preservation...")
    
    # Step 1: Collect all basic blocks and sort them deterministically
    blocks = list(cfg.nodes())
    # Put START first and END last
    start_block = None
    end_block = None
    other_blocks = []
    
    for block in blocks:
        if block.name == "START":
            start_block = block
        elif block.name == "END":
            end_block = block
        else:
            other_blocks.append(block)
    
    # Sort other blocks numerically if possible
    def block_sort_key(block):
        try:
            return int(block.name)
        except ValueError:
            return block.name
    
    other_blocks.sort(key=block_sort_key)
    
    # Combine blocks in order
    sorted_blocks = []
    if start_block:
        sorted_blocks.append(start_block)
    sorted_blocks.extend(other_blocks)
    if end_block:
        sorted_blocks.append(end_block)
    
    # Step 2: Build the IR with instructions from blocks
    ir = []
    block_to_ir_index = {}  # Maps blocks to their starting position in the IR
    
    for block in sorted_blocks:
        if hasattr(block, 'instrlist') and block.instrlist:
            block_to_ir_index[block] = len(ir)
            for instr, _ in block.instrlist:
                ir.append((instr, 1))  # Default offset, will update later
    
    # Step 3: Create a simple mapping for successor blocks
    # Map block name to the actual block object
    name_to_block = {block.name: block for block in sorted_blocks}
    
    # Step 4: Update jump offsets based on the original IR structure
    for i, (instr, _) in enumerate(ir):
        # Find which block contains this instruction
        containing_block = None
        instr_idx_in_block = 0
        
        for block, start_idx in block_to_ir_index.items():
            end_idx = start_idx + len(block.instrlist)
            if start_idx <= i < end_idx:
                containing_block = block
                instr_idx_in_block = i - start_idx
                break
        
        if containing_block is None or not isinstance(instr, ChironAST.ConditionCommand):
            continue
        
        # Special handling for loop counters - preserve their structure carefully
        if (isinstance(instr, ChironAST.ConditionCommand) and 
            hasattr(instr, 'cond') and
            ((hasattr(instr.cond, 'lexpr') and isinstance(instr.cond.lexpr, ChironAST.Var) and ":__rep_counter_" in instr.cond.lexpr.varname) or 
             isinstance(instr.cond, ChironAST.BoolFalse))):
            
            # This is likely a loop condition or a loop jump
            successors = list(cfg.successors(containing_block))
            
            if instr_idx_in_block == len(containing_block.instrlist) - 1 and isinstance(instr.cond, ChironAST.BoolFalse):
                # This is the backward jump at the end of a loop
                # It should jump back to the condition check
                
                # Find the target block that contains the condition check
                target_block = None
                for block in sorted_blocks:
                    if (block in block_to_ir_index and 
                        hasattr(block, 'instrlist') and 
                        len(block.instrlist) > 0 and
                        isinstance(block.instrlist[0][0], ChironAST.ConditionCommand) and
                        hasattr(block.instrlist[0][0], 'cond') and
                        hasattr(block.instrlist[0][0].cond, 'lexpr') and
                        isinstance(block.instrlist[0][0].cond.lexpr, ChironAST.Var) and
                        ":__rep_counter_" in block.instrlist[0][0].cond.lexpr.varname):
                        target_block = block
                        break
                
                if target_block and target_block in block_to_ir_index:
                    target_idx = block_to_ir_index[target_block]
                    offset = target_idx - i
                    ir[i] = (instr, offset)
            
            elif hasattr(instr.cond, 'lexpr') and isinstance(instr.cond.lexpr, ChironAST.Var) and ":__rep_counter_" in instr.cond.lexpr.varname:
                # This is the condition check at the start of a loop
                # It should have a larger offset to skip the loop body if the condition is false
                
                # Find the block that follows the loop body
                # This is usually the end block or a block after all loop blocks
                next_block_idx = sorted_blocks.index(containing_block) + 1
                while next_block_idx < len(sorted_blocks):
                    next_block = sorted_blocks[next_block_idx]
                    if next_block in block_to_ir_index:
                        target_idx = block_to_ir_index[next_block]
                        offset = target_idx - i
                        # For loop conditions, we want to skip to the end if condition is false
                        ir[i] = (instr, offset)
                        break
                    next_block_idx += 1
    
    # Step 5: Final verification - ensure all jumps are valid
    for i, (instr, offset) in enumerate(ir):
        if isinstance(instr, ChironAST.ConditionCommand):
            target_idx = i + offset
            if target_idx < 0 or target_idx >= len(ir):
                print(f"Warning: Jump target {target_idx} is out of bounds for instruction at index {i}")
                # Fix the offset to a safe value
                if offset < 0:  # It's a backward jump
                    # For loop backward jumps, we want to jump to a reasonable point earlier
                    # Find a position with a loop condition if possible
                    for j in range(i-1, 0, -1):
                        if (isinstance(ir[j][0], ChironAST.ConditionCommand) and
                            hasattr(ir[j][0], 'cond') and hasattr(ir[j][0].cond, 'lexpr') and
                            isinstance(ir[j][0].cond.lexpr, ChironAST.Var) and
                            ":__rep_counter_" in ir[j][0].cond.lexpr.varname):
                            ir[i] = (instr, j - i)
                            break
                    else:
                        ir[i] = (instr, -1)  # Jump back one instruction as fallback
                else:  # It's a forward jump
                    ir[i] = (instr, len(ir) - i - 1)  # Jump to the end
    
    return ir
    
def collect_vars_from_expr(expr, var_set):
    """
    Recursively collect variable names from an expression.
    
    Args:
        expr: The expression to analyze
        var_set: Set to add variable names to
    """
    if isinstance(expr, ChironAST.Var):
        var_set.add(expr.varname)
    elif hasattr(expr, 'lexpr') and hasattr(expr, 'rexpr'):
        collect_vars_from_expr(expr.lexpr, var_set)
        collect_vars_from_expr(expr.rexpr, var_set)
    elif hasattr(expr, 'expr'):
        collect_vars_from_expr(expr.expr, var_set)

def collect_all_variables(ir):
    """
    Collect all variable names from an IR.
    """
    variables = set()
    
    for instr, _ in ir:
        # Check variable uses
        if hasattr(instr, 'rexpr'):
            collect_vars_from_expr(instr.rexpr, variables)
        
        if hasattr(instr, 'cond'):
            collect_vars_from_expr(instr.cond, variables)
            
        if hasattr(instr, 'expr'):
            collect_vars_from_expr(instr.expr, variables)
            
        if hasattr(instr, 'xcor') and hasattr(instr, 'ycor'):
            collect_vars_from_expr(instr.xcor, variables)
            collect_vars_from_expr(instr.ycor, variables)
        
        # Check variable definitions
        if hasattr(instr, 'lvar') and isinstance(instr.lvar, ChironAST.Var):
            variables.add(instr.lvar.varname)
    
    return variables

if __name__ == "__main__":
    print(Release)
    print(
        """
    ░█████╗░██╗░░██╗██╗██████╗░░█████╗░███╗░░██╗
    ██╔══██╗██║░░██║██║██╔══██╗██╔══██╗████╗░██║
    ██║░░╚═╝███████║██║██████╔╝██║░░██║██╔██╗██║
    ██║░░██╗██╔══██║██║██╔══██╗██║░░██║██║╚████║
    ╚█████╔╝██║░░██║██║██║░░██║╚█████╔╝██║░╚███║
    ░╚════╝░╚═╝░░╚═╝╚═╝╚═╝░░╚═╝░╚════╝░╚═╝░░╚══╝
    """
    )

    # process the command-line arguments
    cmdparser = argparse.ArgumentParser(
        description="Program Analysis Framework for ChironLang Programs."
    )

    # add arguments for parsing command-line arguments
    cmdparser.add_argument(
        "-p",
        "--ir",
        action="store_true",
        help="pretty printing the IR of a Chiron program to stdout (terminal)",
    )
    # added static single assignment option
    cmdparser.add_argument(
        "-ssa",
        "--static_single_assignment",
        action="store_true",
        help="Apply SSA form conversion and destruction to the program"
    )
    # Added dead code elimination option
    cmdparser.add_argument(
        "-dce",
        "--dead_code_elimination",
        action="store_true",
        help="Apply Dead Code Elimination optimization on SSA form",
    )
    cmdparser.add_argument(
        "-r",
        "--run",
        action="store_true",
        help="execute Chiron program, the figure/shapes the turle draws is shown in a UI.",
    )

    cmdparser.add_argument(
        "-gr",
        "--fuzzer_gen_rand",
        action="store_true",
        help="Generate random input seeds for the fuzzer before fuzzing starts.",
    )

    cmdparser.add_argument(
        "-b", "--bin", action="store_true", help="load binary IR of a Chiron program"
    )
    
    cmdparser.add_argument(
        "-k", "--hooks", action="store_true", help="Run hooks for Kachua."
    )

    cmdparser.add_argument(
        "-z",
        "--fuzz",
        action="store_true",
        help="Run fuzzer on a Chiron program (seed values with '-d' or '--params' flag needed.)",
    )
    cmdparser.add_argument(
        "-t",
        "--timeout",
        default=10,
        type=float,
        help="Timeout Parameter for Analysis (in secs). This is the total timeout.",
    )
    cmdparser.add_argument("progfl")

    # passing variable values via command line. E.g.
    # ./chiron.py -r <program file> --params '{":x" : 10, ":z" : 20, ":w" : 10, ":k" : 2}'
    cmdparser.add_argument(
        "-d",
        "--params",
        default=dict(),
        type=ast.literal_eval,
        help="pass variable values to Chiron program in python dictionary format",
    )
    cmdparser.add_argument(
        "-c",
        "--constparams",
        default=dict(),
        type=ast.literal_eval,
        help="pass variable(for which you have to find values using circuit equivalence) values to Chiron program in python dictionary format",
    )
    cmdparser.add_argument(
        "-se",
        "--symbolicExecution",
        action="store_true",
        help="Run Symbolic Execution on a Chiron program (seed values with '-d' or '--params' flag needed) to generate test cases along all possible paths.",
    )
    # TODO: add additional arguments for parsing command-line arguments

    cmdparser.add_argument(
        "-ai",
        "--abstractInterpretation",
        action="store_true",
        help="Run abstract interpretation on a Chiron Program.",
    )
    cmdparser.add_argument(
        "-dfa",
        "--dataFlowAnalysis",
        action="store_true",
        help="Run data flow analysis using worklist algorithm on a Chiron Program.",
    )

    cmdparser.add_argument(
        "-sbfl",
        "--SBFL",
        action="store_true",
        help="Run Spectrum-basedFault localizer on Chiron program",
    )
    cmdparser.add_argument("-bg", "--buggy", help="buggy Chiron program path", type=str)
    cmdparser.add_argument(
        "-vars",
        "--inputVarsList",
        help="A list of input variables of given Chiron program",
        type=str,
    )
    cmdparser.add_argument(
        "-nt", "--ntests", help="number of tests to generate", default=10, type=int
    )
    cmdparser.add_argument(
        "-pop",
        "--popsize",
        help="population size for Genetic Algorithm.",
        default=100,
        type=int,
    )
    cmdparser.add_argument(
        "-cp", "--cxpb", help="cross-over probability", default=1.0, type=float
    )
    cmdparser.add_argument(
        "-mp", "--mutpb", help="mutation probability", default=1.0, type=float
    )
    cmdparser.add_argument(
        "-cfg_gen",
        "--control_flow",
        help="Generate the CFG of the given turtle program",
        action="store_true",
    )
    cmdparser.add_argument(
        "-cfg_dump",
        "--dump_cfg",
        help="Generate the CFG of the given turtle program",
        action="store_true",
    )
    cmdparser.add_argument(
        "-dump",
        "--dump_ir",
        help="Dump the IR to a .kw (pickle file)",
        action="store_true",
    )
    cmdparser.add_argument(
        "-ng",
        "--ngen",
        help="number of times Genetic Algorithm iterates",
        default=100,
        type=int,
    )
    cmdparser.add_argument(
        "-vb",
        "--verbose",
        help="To display computation to Console",
        default=True,
        type=bool,
    )

    args = cmdparser.parse_args()
    ir = ""

    if not (type(args.params) is dict):
        raise ValueError("Wrong type for command line arguement '-d' or '--params'.")

    # Instantiate the irHandler
    # this object is passed around everywhere.
    irHandler = IRHandler(ir)

    # generate IR
    if args.bin:
        ir = irHandler.loadIR(args.progfl)
    else:
        parseTree = getParseTree(args.progfl)
        astgen = astGenPass()
        ir = astgen.visitStart(parseTree)

    # Set the IR of the program.
    irHandler.setIR(ir)

    # generate control_flow_graph from IR statements.
    if args.control_flow:
        cfg = cfgB.buildCFG(ir, "control_flow_graph", False)
        irHandler.setCFG(cfg)

    else:
        irHandler.setCFG(None)

    if args.dump_cfg:
        # Added below 2 lines
        cfg = cfgB.buildCFG(ir, "control_flow_graph", False)
        irHandler.setCFG(cfg)
        cfgB.dumpCFG(cfg, "control_flow_graph")
        # set the cfg of the program.

    if args.ir:
        irHandler.pretty_print(irHandler.ir)

    if args.abstractInterpretation:
        AISub.analyzeUsingAI(irHandler)
        print("== Abstract Interpretation ==")

    if args.dataFlowAnalysis:
        irOpt = DFASub.optimizeUsingDFA(irHandler)
        print("== Optimized IR ==")
        irHandler.pretty_print(irHandler.ir)

    if args.dump_ir:
        irHandler.pretty_print(irHandler.ir)
        irHandler.dumpIR("optimized.kw", irHandler.ir)

    if args.static_single_assignment:
        print("\n========== ORIGINAL IR BEFORE SSA ==========\n")
        irHandler.pretty_print(irHandler.ir)

        # Store the original IR for later reference
        original_ir = list(irHandler.ir)  # Make a copy

        print("\n===== Converting to SSA Form =====")
        if not irHandler.cfg:
            # Generate CFG if not already generated
            cfg = cfgB.buildCFG(ir, "control_flow_graph", False)
            irHandler.setCFG(cfg)
        
        # Convert to SSA form
        ssa_converter = SSAConverter(irHandler.cfg)
        ssa_cfg = ssa_converter.convert_to_ssa()
        irHandler.setCFG(ssa_cfg)
        
        # Convert CFG to IR and update the IR handler
        ssa_ir = cfg_to_ir(ssa_cfg)
        irHandler.setIR(ssa_ir)
        
        # Print SSA IR
        print("\n========== IR AFTER SSA CONVERSION ==========\n")
        irHandler.pretty_print(irHandler.ir)
        
        if args.dump_cfg:
            cfgB.dumpCFG(ssa_cfg, "ssa_form_cfg")
            print("SSA form CFG dumped to ssa_form_cfg.png")
        
        print("\n===== Converting back from SSA Form =====")
        # Convert back from SSA form
        ssa_destroyer = SSADestroyer(irHandler.cfg)
        normal_cfg = ssa_destroyer.convert_from_ssa()
        irHandler.setCFG(normal_cfg)
        
        # Convert CFG to IR and update the IR handler
        post_ssa_ir = cfg_to_ir(normal_cfg)
                
        # Update IR
        irHandler.setIR(post_ssa_ir)
        
        # Print post-SSA IR
        print("\n========== IR AFTER SSA DESTRUCTION ==========\n")
        irHandler.pretty_print(irHandler.ir)
        
        if args.dump_cfg:
            cfgB.dumpCFG(normal_cfg, "post_ssa_cfg")
            print("Post-SSA CFG dumped to post_ssa_cfg.png")


    if args.dead_code_elimination:
        print("\n===== Starting Dead Code Elimination =====")
        # Check if we have a CFG
        if not irHandler.cfg:
            # Generate CFG if not already generated
            cfg = cfgB.buildCFG(irHandler.ir, "control_flow_graph", False)
            irHandler.setCFG(cfg)
        
        # CHECKPOINT 1: Print IR and dump CFG BEFORE SSA conversion
        print("\n========== IR BEFORE SSA CONVERSION ==========\n")
        irHandler.pretty_print(irHandler.ir)
        cfgB.dumpCFG(irHandler.cfg, "control_flow_graph")
        print("CFG before SSA conversion dumped to control_flow_graph.png")
        
        # Convert to SSA form if not already in SSA form
        if not args.static_single_assignment:
            print("\n===== Converting to SSA Form =====")
            ssa_converter = SSAConverter(irHandler.cfg)
            ssa_cfg = ssa_converter.convert_to_ssa()
            irHandler.setCFG(ssa_cfg)
            
            # Convert CFG to IR and update the IR handler
            ssa_ir = cfg_to_ir(ssa_cfg)
            irHandler.setIR(ssa_ir)
        
        # CHECKPOINT 2: Print IR and dump CFG AFTER SSA conversion
        print("\n========== IR AFTER SSA CONVERSION ==========\n")
        irHandler.pretty_print(irHandler.ir)
        cfgB.dumpCFG(irHandler.cfg, "ssa_form_cfg")
        print("CFG after SSA conversion dumped to ssa_form_cfg.png")
        
        # Run dead code elimination
        dce = DeadCodeElimination(irHandler.cfg)
        optimized_cfg = dce.eliminate_dead_code()
        irHandler.setCFG(optimized_cfg)
        
        # Update IR
        optimized_ir = cfg_to_ir(optimized_cfg)
        irHandler.setIR(optimized_ir)
        
        # CHECKPOINT 3: Print IR and dump CFG AFTER dead code elimination
        print("\n========== IR AFTER DEAD CODE ELIMINATION ==========\n")
        irHandler.pretty_print(irHandler.ir)
        cfgB.dumpCFG(irHandler.cfg, "after_dce_cfg")
        print("CFG after dead code elimination dumped to after_dce_cfg.png")
        
        # Convert back from SSA form if needed
        if not args.static_single_assignment:
            print("\n===== Converting back from SSA Form =====")
            ssa_destroyer = SSADestroyer(irHandler.cfg)
            normal_cfg = ssa_destroyer.convert_from_ssa()
            irHandler.setCFG(normal_cfg)
            
            # Convert CFG to IR and update the IR handler
            post_ssa_ir = cfg_to_ir(normal_cfg)
            irHandler.setIR(post_ssa_ir)
        
        # CHECKPOINT 4: Print IR and dump CFG AFTER converting back from SSA
        print("\n========== IR AFTER SSA DESTRUCTION ==========\n")
        irHandler.pretty_print(irHandler.ir)
        cfgB.dumpCFG(irHandler.cfg, "final_cfg")
        print("CFG after SSA destruction dumped to final_cfg.png")

    if args.symbolicExecution:
        print("symbolicExecution")
        if not args.params:
            raise RuntimeError(
                "Symbolic Execution needs initial seed values. Specify using '-d' or '--params' flag."
            )
        """
        How to run symbolicExecution?
        # ./chiron.py -t 100 --symbolicExecution example/example2.tl -d '{":dir": 10, ":move": -90}'
        """
        se.symbolicExecutionMain(
            irHandler, args.params, args.constparams, timeLimit=args.timeout
        )

    if args.fuzz:
        if not args.params:
            raise RuntimeError(
                "Fuzzing needs initial seed values. Specify using '-d' or '--params' flag."
            )
        """
        How to run fuzzer?
        # ./chiron.py -t 100 --fuzz example/example1.tl -d '{":x": 5, ":y": 100}'
        # ./chiron.py -t 100 --fuzz example/example2.tl -d '{":dir": 3, ":move": 5}'
        """
        fuzzer = Fuzzer(irHandler, args)
        cov, corpus = fuzzer.fuzz(
            timeLimit=args.timeout, generateRandom=args.fuzzer_gen_rand
        )
        print(f"Coverage : {cov.total_metric},\nCorpus:")
        for index, x in enumerate(corpus):
            print(f"\tInput {index} : {x.data}")

    if args.run:
        # for stmt,pc in ir:
        #     print(str(stmt.__class__.__bases__[0].__name__),pc)

        inptr = ConcreteInterpreter(irHandler, args)
        terminated = False
        inptr.initProgramContext(args.params)
        while True:
            terminated = inptr.interpret()
            if terminated:
                break
        print("Program Ended.")
        print()
        print("Press ESCAPE to exit")
        turtle.listen()
        turtle.onkeypress(stopTurtle, "Escape")
        turtle.mainloop()

    if args.SBFL:
        if not args.buggy:
            raise RuntimeError(
                "test-suite generator needs buggy program also. Specify using '--buggy' flag."
            )
        if not args.inputVarsList:
            raise RuntimeError(
                "please specify input variable list. Specify using '--inputVarsList'  or '-vars' flag."
            )
        """
        How to run SBFL?
        Consider we have :
            a correct program = sbfl1.tl
            corresponding buggy program sbfl1_buggy.tl
            input variables = :x, :y :z
            initial test-suite size = 20.
            Maximum time(in sec) to run a test-case = 10.
        Since we want to generate optimized test suite using genetic-algorithm,
        therefore we also need to provide:
            the intial population size = 100
            cross-over probabiliy = 1.0
            mutation probability = 1.0
            number of times GA to iterate = 100, therefore
        command : ./chiron.py --SBFL ./example/sbfl1.tl --buggy ./example/sbfl1_buggy.tl \
            -vars '[":x", ":y", ":z"]' --timeout 1 --ntests 20 --popsize 100 --cxpb 1.0 --mutpb 1.0 --ngen 100 --verbose True
        Note : if a program doesn't take any input vars them pass argument -vars as '[]'
        """

        print("SBFL...")
        # generate IR of correct program
        parseTree = getParseTree(args.progfl)
        astgen = astGenPass()
        ir1 = astgen.visitStart(parseTree)

        # generate IR of buggy program
        parseTree = getParseTree(args.buggy)
        astgen = astGenPass()
        ir2 = astgen.visitStart(parseTree)

        irhandler1 = IRHandler(ir1)
        irhandler2 = IRHandler(ir2)

        # Generate Optimized Test Suite.
        (
            original_testsuite,
            original_test,
            optimized_testsuite,
            optimized_test,
            spectrum,
        ) = testsuiteGenerator(
            irhandler1=irhandler1,
            irhandler2=irhandler2,
            inputVars=eval(args.inputVarsList),
            Ntests=args.ntests,
            timeLimit=args.timeout,
            popsize=args.popsize,
            cxpb=args.cxpb,
            mutpb=args.mutpb,
            ngen=args.ngen,
            verbose=args.verbose,
        )
        # compute ranks of components and write to file
        computeRanks(
            spectrum=spectrum,
            outfilename="{}_componentranks.csv".format(args.buggy.replace(".tl", "")),
        )

        # write all output data.
        with open(
            "{}_tests-original_act-mat.csv".format(args.buggy.replace(".tl", "")), "w"
        ) as file:
            writer = csv.writer(file)
            writer.writerows(original_testsuite)

        with open(
            "{}_tests-original.csv".format(args.buggy.replace(".tl", "")), "w"
        ) as file:
            writer = csv.writer(file)
            for test in original_test:
                writer.writerow([test])

        with open(
            "{}_tests-optimized_act-mat.csv".format(args.buggy.replace(".tl", "")), "w"
        ) as file:
            writer = csv.writer(file)
            writer.writerows(optimized_testsuite)

        with open(
            "{}_tests-optimized.csv".format(args.buggy.replace(".tl", "")), "w"
        ) as file:
            writer = csv.writer(file)
            for test in optimized_test:
                writer.writerow([test])

        with open("{}_spectrum.csv".format(args.buggy.replace(".tl", "")), "w") as file:
            writer = csv.writer(file)
            writer.writerows(spectrum)
        print("DONE..")