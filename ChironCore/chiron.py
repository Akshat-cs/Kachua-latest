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
# Add SSA conversion imports
from SSAConverter import SSAConverter
from SSADestroyer import SSADestroyer

def cleanup():
    pass

def stopTurtle():
    turtle.bye()

def cfg_to_ir(cfg):
    """
    Convert a CFG to IR with correctly calculated jump offsets
    based on the control flow structure.
    """
    # Step 1: Collect all basic blocks and their instructions
    block_instructions = {}
    block_line_numbers = {}
    
    for block in cfg.nodes():
        if not hasattr(block, 'instrlist') or not block.instrlist:
            continue
            
        block_instructions[block] = block.instrlist
        
        # Store the lowest line number in this block for sorting
        min_line = min(line_num for _, line_num in block.instrlist)
        block_line_numbers[block] = min_line
    
    # Step 2: Build a deterministic block order based on line numbers
    ordered_blocks = sorted(block_instructions.keys(), key=lambda b: block_line_numbers[b])
    
    # Step 3: Map each block to its successor blocks
    block_successors = {}
    block_predecessors = {}
    for block in ordered_blocks:
        successors = {}
        for succ in cfg.successors(block):
            edge_label = cfg.get_edge_label(block, succ)
            successors[edge_label] = succ
        block_successors[block] = successors
        
        # Track predecessors
        for pred in cfg.predecessors(block):
            if block not in block_predecessors:
                block_predecessors[block] = []
            block_predecessors[block].append(pred)
    
    # Step 4: Build the IR with correct block ordering
    ir = []
    block_start_indices = {}  # Maps blocks to their starting position in IR
    
    # First pass: add all instructions from blocks in order
    for block in ordered_blocks:
        block_start_indices[block] = len(ir)
        
        for instr, _ in block_instructions[block]:
            ir.append((instr, 1))  # Default jump offset
    
    # Step 5: Calculate correct jump offsets based on CFG structure
    for i, (instr, _) in enumerate(ir):
        if isinstance(instr, ChironAST.ConditionCommand):
            # Find the block containing this instruction
            containing_block = None
            for block in ordered_blocks:
                start_idx = block_start_indices[block]
                end_idx = start_idx + len(block_instructions[block])
                if start_idx <= i < end_idx:
                    containing_block = block
                    break
            
            if not containing_block:
                continue
            
            # Handling condition command
            successors = block_successors.get(containing_block, {})
            
            if isinstance(instr.cond, ChironAST.BoolFalse):
                # False jump - look for the next block to jump to
                target_block = successors.get('Cond_False')
                
                if target_block and target_block in block_start_indices:
                    target_idx = block_start_indices[target_block]
                    offset = target_idx - i
                    ir[i] = (instr, offset)
            else:
                # Condition check - handle true/false branches
                false_target = successors.get('Cond_False')
                
                if false_target and false_target in block_start_indices:
                    false_idx = block_start_indices[false_target]
                    offset = false_idx - i
                    ir[i] = (instr, offset)
    
    # Step 6: Intelligent fallback for unresolved jumps
    for i, (instr, offset) in enumerate(ir):
        if isinstance(instr, ChironAST.ConditionCommand):
            # Ensure jump is within IR bounds
            if i + offset >= len(ir) or i + offset < 0:
                # Find the closest block beyond the current point
                next_blocks = [
                    block_start_indices[block] 
                    for block in ordered_blocks 
                    if block_start_indices[block] > i
                ]
                
                if next_blocks:
                    closest_block_idx = min(next_blocks)
                    ir[i] = (instr, closest_block_idx - i)
                else:
                    # Fallback to end of IR
                    ir[i] = (instr, len(ir) - i - 1)
    
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
    cmdparser.add_argument(
        "-ssa",
        "--static_single_assignment",
        action="store_true",
        help="Apply SSA form conversion and destruction to the program"
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