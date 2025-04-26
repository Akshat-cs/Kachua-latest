#!/usr/bin/python3
# -*- coding: utf-8 -*-
# SSA Converter for ChironLang

import os
import sys
import copy
import re
import networkx as nx
from collections import defaultdict

# Import necessary Chiron modules
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from ChironAST import ChironAST

class SSAConverter:
    def __init__(self, cfg):
        self.cfg = cfg
        self.dominators = {}
        self.immediate_dominators = {}
        self.dominator_tree = {}
        self.dominance_frontier = {}

        # For variable tracking
        self.all_variables = set()        # All variables in the program
        self.variable_defs = defaultdict(set)  # Maps var -> set of blocks that define it
        self.variable_versions = {}       # Maps var -> current version number
        self.variable_stacks = defaultdict(list)  # Maps var -> stack of SSA versions

    def convert_to_ssa(self):
        """
        Convert the CFG to SSA form:
        1. Find all variables and their definitions
        2. Compute dominance information
        3. Identify loop structures
        4. Place phi functions at appropriate merge points
        5. Rename variables to their SSA versions
        """
        print("\n===== SSA CONVERSION STARTED =====")

        # Find all variables and their definitions
        self._find_all_variables()

        # Compute dominance information
        self._compute_dominance_info()

        # Place phi functions
        self._place_phi_functions()

        # Rename variables
        self._rename_variables()

        print("\n===== SSA CONVERSION COMPLETED =====")

        return self.cfg

    def _dump_all_blocks_instructions(self, phase_name):
        """
        Dump the instruction list for all blocks in sequence to a text file
        
        Args:
            phase_name: String identifying the current phase of SSA conversion
        """
        # Create a filename based on the phase name
        filename = f"ssa_{phase_name}.txt"
        
        # Get all blocks and sort them for consistent output
        all_blocks = list(self.cfg.nodes())
        
        # Try to sort blocks by their name for readable output
        try:
            # First try to sort numeric blocks by their integer value
            numeric_blocks = [b for b in all_blocks if hasattr(b, 'name') and b.name.isdigit()]
            numeric_blocks.sort(key=lambda b: int(b.name))
            
            # Then handle special blocks like START and END
            start_block = [b for b in all_blocks if hasattr(b, 'name') and b.name == "START"]
            end_block = [b for b in all_blocks if hasattr(b, 'name') and b.name == "END"]
            
            # Other non-numeric blocks
            other_blocks = [b for b in all_blocks if hasattr(b, 'name') and not b.name.isdigit() 
                            and b.name != "START" and b.name != "END"]
            other_blocks.sort(key=lambda b: b.name)
            
            # Combine all blocks in logical order: START, numeric, other, END
            sorted_blocks = start_block + numeric_blocks + other_blocks + end_block
        except:
            # Fallback if sorting fails
            sorted_blocks = [b for b in all_blocks if hasattr(b, 'name')]
            sorted_blocks.sort(key=lambda b: str(b.name))
        
        # Open file for writing
        with open(filename, 'w') as f:
            f.write(f"===== INSTRUCTION LISTING {phase_name.upper().replace('_', ' ')} =====\n\n")
            
            # Write each block's instructions
            for block in sorted_blocks:
                if hasattr(block, 'name'):
                    f.write(f"Block {block.name}:\n")
                    
                    if hasattr(block, 'instrlist') and block.instrlist:
                        # Sort by line number for consistency
                        sorted_instrs = sorted(block.instrlist, key=lambda x: x[1])
                        
                        for i, (instr, line_num) in enumerate(sorted_instrs):
                            # Special handling for PHI instructions to make them more readable
                            if isinstance(instr, ChironAST.PhiInstruction):
                                target = instr.target_var.varname
                                sources = []
                                for j, (src_var, src_block) in enumerate(zip(instr.source_vars, instr.source_blocks)):
                                    block_name = src_block.name if hasattr(src_block, 'name') else f"block{j}"
                                    sources.append(f"{src_var.varname} from {block_name}")
                                
                                phi_str = f"{target} = φ({', '.join(sources)})"
                                f.write(f"  [{i}] {phi_str} at line {line_num}\n")
                            else:
                                f.write(f"  [{i}] {instr} at line {line_num}\n")
                    else:
                        f.write("  No instructions\n")
                    
                    f.write("\n")
            
            # Write divider at the end of the file
            f.write("="*50 + "\n")
        
        print(f"Dumped instruction listing to {filename}")

    def _find_all_variables(self):
        """
        Find all variables and their definitions in the program
        """
        print("\n===== FINDING ALL VARIABLES =====")

        # First pass: collect all variables and their definitions
        for block in self.cfg.nodes():
            if not hasattr(block, 'instrlist'):
                continue

            for instr, _ in block.instrlist:
                # Check for variable definitions
                if hasattr(instr, 'lvar') and isinstance(instr.lvar, ChironAST.Var):
                    var_name = instr.lvar.varname
                    # Strip any existing SSA suffix
                    base_name = self._get_base_name(var_name)
                    self.all_variables.add(base_name)
                    self.variable_defs[base_name].add(block)

                # Check for variable uses
                self._collect_variables_from_instruction(instr)

        # Initialize version counters for all variables
        self.variable_versions = {var: 0 for var in self.all_variables}

        print(f"Found {len(self.all_variables)} variables:")
        for var in sorted(self.all_variables):
            print(f"  {var} - defined in {len(self.variable_defs.get(var, []))} blocks")

    def _get_base_name(self, var_name):
        """
        Get the base name of a variable (without SSA suffix)
        """
        # Special case for loop counter variables
        if ":__rep_counter_" in var_name:
            # Extract just the counter number as part of the base name
            match = re.match(r'(:__rep_counter_\d+)(_\d+)?$', var_name)
            if match:
                return match.group(1)
        
        # Regular SSA variables
        match = re.match(r'(.+)_\d+$', var_name)
        if match:
            return match.group(1)

        return var_name

    def _collect_variables_from_instruction(self, instr):
        """
        Collect all variables used in an instruction
        """
        # Assignment right-hand side
        if hasattr(instr, 'rexpr'):
            self._collect_variables_from_expression(instr.rexpr)

        # Condition
        if hasattr(instr, 'cond'):
            self._collect_variables_from_expression(instr.cond)

        # Move expression
        if hasattr(instr, 'expr'):
            self._collect_variables_from_expression(instr.expr)

        # Goto coordinates
        if hasattr(instr, 'xcor') and hasattr(instr, 'ycor'):
            self._collect_variables_from_expression(instr.xcor)
            self._collect_variables_from_expression(instr.ycor)

    def _collect_variables_from_expression(self, expr):
        """
        Recursively collect all variables from an expression
        """
        if isinstance(expr, ChironAST.Var):
            base_name = self._get_base_name(expr.varname)
            self.all_variables.add(base_name)
        elif hasattr(expr, 'lexpr') and hasattr(expr, 'rexpr'):
            self._collect_variables_from_expression(expr.lexpr)
            self._collect_variables_from_expression(expr.rexpr)
        elif hasattr(expr, 'expr'):
            self._collect_variables_from_expression(expr.expr)

    def _compute_dominance_info(self):
        """
        Compute dominance information for the CFG:
        1. Immediate dominators
        2. Dominator tree
        3. Dominance frontiers
        """
        print("\n===== COMPUTING DOMINANCE INFORMATION =====")

        # Create a graph for NetworkX
        G = nx.DiGraph()
        for block in self.cfg.nodes():
            for succ in self.cfg.successors(block):
                G.add_edge(block, succ)

        # Find the entry node
        entry_block = None
        for block in self.cfg.nodes():
            if block.name == "START" or self.cfg.in_degree(block) == 0:
                entry_block = block
                break

        if not entry_block:
            print("ERROR: No entry block found in CFG")
            return

        print(f"Entry block: {entry_block.name}")

        # Use NetworkX to calculate immediate dominators
        try:
            # Compute immediate dominators
            self.immediate_dominators = nx.immediate_dominators(G, entry_block)
            print("Successfully computed immediate dominators")

            # Compute dominators
            self.dominators = {}
            for node in G.nodes():
                self.dominators[node] = set()
                current = node
                while current != entry_block and current is not None:
                    idom = self.immediate_dominators.get(current)
                    if idom and idom != current:
                        self.dominators[node].add(idom)
                        current = idom
                    else:
                        break
                # Always add entry_block except for itself
                if node != entry_block:
                    self.dominators[node].add(entry_block)

            # Build dominator tree
            self.dominator_tree = defaultdict(set)
            for block, idom in self.immediate_dominators.items():
                if idom is not None and idom != block:
                    self.dominator_tree[idom].add(block)
                    print(f"Added {block.name} as child of {idom.name} in dominator tree")
        except Exception as e:
            print(f"Error in dominators calculation: {e}")
            return

        # Compute dominance frontiers
        try:
            self._compute_dominance_frontiers()
            # Print a summary of dominance frontiers
            self._print_dominance_frontiers_summary()
            print("Successfully computed dominance frontiers")
        except Exception as e:
            print(f"Error in dominance frontier calculation: {e}")

    def _compute_dominance_frontiers(self):
        """
        Compute the dominance frontier for each block.
        The dominance frontier of a block B is the set of all nodes where B's dominance ends.
        """
        # Initialize dominance frontiers
        self.dominance_frontier = {block: set() for block in self.cfg.nodes()}

        # For each block in the CFG
        for block in self.cfg.nodes():
            # For each successor of the block
            for succ in self.cfg.successors(block):
                # If the successor is not immediately dominated by the block
                if self.immediate_dominators.get(succ) != block:
                    self.dominance_frontier[block].add(succ)

        # Propagate dominance frontiers up the dominator tree
        for block in sorted(self.cfg.nodes(), key=lambda x: len(self.dominator_tree.get(x, set())), reverse=True):
            # For each child in the dominator tree
            for dom_child in self.dominator_tree.get(block, set()):
                # For each block in the child's dominance frontier
                for frontier_block in self.dominance_frontier.get(dom_child, set()):
                    # If the block doesn't strictly dominate the frontier block
                    if self.immediate_dominators.get(frontier_block) != block:
                        # Add to the block's dominance frontier
                        self.dominance_frontier[block].add(frontier_block)

    def _print_dominance_frontiers_summary(self):
        """
        Print a detailed summary of dominance frontiers for all blocks
        """
        print("\n===== DOMINANCE FRONTIERS =====")
        
        # Sort blocks by name for consistent output
        sorted_blocks = sorted(self.cfg.nodes(), key=lambda b: b.name if hasattr(b, 'name') else "")
        
        # Print dominance frontier for each block
        for block in sorted_blocks:
            if hasattr(block, 'name'):
                df = self.dominance_frontier.get(block, set())
                df_names = [b.name for b in df] if df else []
                df_names.sort()  # Sort for consistent output
                
                # Format the dominance frontier as a comma-separated list in braces
                frontier_str = "{" + ", ".join(df_names) + "}" if df_names else "{}"
                print(f"DF({block.name}) = {frontier_str}")

    def _place_phi_functions(self):
        """
        Place phi functions at join points using the iterated dominance frontier algorithm
        from the Cytron et al. paper
        """
        print("\n===== PLACING PHI FUNCTIONS =====")

        # For each variable
        for var_name in sorted(self.all_variables):
            # Skip variables without definitions
            if not self.variable_defs[var_name]:
                continue

            print(f"Processing variable: {var_name}")
            
            # Compute iterated dominance frontier for blocks that define this variable
            phi_blocks = set()  # Blocks that need phi functions for this variable
            worklist = list(self.variable_defs[var_name])
            
            # Process the worklist to compute iterated dominance frontier
            while worklist:
                block = worklist.pop()
                
                # For each block in the dominance frontier
                for df_block in self.dominance_frontier.get(block, set()):
                    if df_block not in phi_blocks:
                        # This block needs a phi function
                        phi_blocks.add(df_block)
                        
                        # If this block doesn't already have a definition of the variable,
                        # add it to the worklist for further propagation
                        if df_block not in self.variable_defs[var_name]:
                            self.variable_defs[var_name].add(df_block)
                            worklist.append(df_block)
            
            # Insert phi functions in the calculated blocks
            for block in sorted(phi_blocks, key=lambda b: 
                            (-1 if b.name == "START" else 
                            (float('inf') if b.name == "END" else 
                                int(b.name)))):
                self._insert_phi_function(var_name, block)

    def _insert_phi_function(self, var_name, block):
        """
        Insert a phi function for variable var_name at the beginning of block
        """
        print(f"  Placing phi function for {var_name} in block {block.name}")
        
        # Count predecessors
        predecessors = list(self.cfg.predecessors(block))
        if not predecessors:
            print(f"Warning: Block {block.name} has no predecessors, skipping phi function")
            return
            
        # Check if a phi function for this variable already exists in this block
        if hasattr(block, 'instrlist'):
            for instr, _ in block.instrlist:
                if isinstance(instr, ChironAST.PhiInstruction):
                    if self._get_base_name(instr.target_var.varname) == var_name:
                        print(f"    Phi function for {var_name} already exists in block {block.name}")
                        return
        
        # Create phi function
        target_var = ChironAST.Var(var_name)
        source_vars = []
        source_blocks = []
        
        # Add a source for each predecessor
        for pred in sorted(predecessors, key=lambda x: 
                        (-1 if x.name == "START" else 
                        (float('inf') if x.name == "END" else 
                        int(x.name)))):
            source_vars.append(ChironAST.Var(var_name))
            source_blocks.append(pred)
        
        # Create the phi instruction
        phi = ChironAST.PhiInstruction(target_var, source_vars, source_blocks)
        
        # Determine line number for the phi function - it should be at the beginning of the block
        if not hasattr(block, 'instrlist') or not block.instrlist:
            # If block has no instructions, use a line number based on predecessors
            max_pred_line = 0
            for pred in predecessors:
                if hasattr(pred, 'instrlist') and pred.instrlist:
                    for _, line_num in pred.instrlist:
                        max_pred_line = max(max_pred_line, line_num)
            line_num = max_pred_line + 1
            block.instrlist = [(phi, line_num)]
        else:
            # Find existing phi functions
            existing_phis = [(i, instr, line) for i, (instr, line) in enumerate(block.instrlist) 
                            if isinstance(instr, ChironAST.PhiInstruction)]
            
            if existing_phis:
                # Insert among existing phi functions with a logical line number
                min_phi_line = min(line for _, _, line in existing_phis)
                
                # Insert the new phi function
                new_instrlist = list(block.instrlist)
                # Use a slightly lower line number to ensure phi functions come first
                new_instrlist.append((phi, min_phi_line - 0.1))
                # Sort by line number
                new_instrlist.sort(key=lambda x: x[1])
                block.instrlist = new_instrlist
            else:
                # Insert at the beginning with a lower line number
                min_line = min(line for _, line in block.instrlist)
                
                # Create a new list with phi function first
                new_instrlist = [(phi, min_line - 1)]
                new_instrlist.extend(block.instrlist)
                block.instrlist = new_instrlist

    def _rename_variables(self):
        """
        Rename variables to their SSA versions
        This implements the algorithm from the Cytron paper
        """
        print("\n===== RENAMING VARIABLES =====")

        # Initialize stacks for each variable
        self.variable_stacks = {var: [] for var in self.all_variables}

        # Add variable version 0 to each stack (for entry values)
        for var in self.all_variables:
            self.variable_versions[var] = 0
            new_name = f"{var}_0"
            self.variable_stacks[var].append(new_name)

        # Find the entry block
        entry_block = None
        for block in self.cfg.nodes():
            if block.name == "START" or self.cfg.in_degree(block) == 0:
                entry_block = block
                print(f"[Entry Found] Entry block set to: {block.name}")
                break

        if not entry_block:
            print("ERROR: No entry block found in CFG")
            return

        self._rename_variables_in_block(entry_block)

    def _rename_variables_in_block(self, block):
        """
        Rename all variables in a block and its dominator tree children
        """
        if not hasattr(block, 'instrlist'):
            return
            
        print(f"\n[Block] Renaming variables in block: {block.name}")
        
        # Save the current variable stacks to restore later
        old_stacks = {var: list(stack) for var, stack in self.variable_stacks.items()}

        # Process each instruction in the block
        for i, (instr, line_num) in enumerate(list(block.instrlist)):
            
            # First handle phi functions
            if isinstance(instr, ChironAST.PhiInstruction):
                var_name = self._get_base_name(instr.target_var.varname)
                self.variable_versions[var_name] += 1
                new_version = self.variable_versions[var_name]
                new_name = f"{var_name}_{new_version}"
                instr.target_var.varname = new_name
                self.variable_stacks[var_name].append(new_name)
            else:
                self._rename_uses_in_instruction(instr)

                # Then handle definitions
                if hasattr(instr, 'lvar') and isinstance(instr.lvar, ChironAST.Var):
                    var_name = self._get_base_name(instr.lvar.varname)
                    self.variable_versions[var_name] += 1
                    new_version = self.variable_versions[var_name]
                    new_name = f"{var_name}_{new_version}"
                    old_name = instr.lvar.varname
                    
                    # Special handling for loop counter variables
                    if ":__rep_counter_" in var_name:
                        # Create a new Var object instead of modifying the existing one
                        new_var = ChironAST.Var(new_name)
                        instr.lvar = new_var
                    else:
                        # For other variables, modify in place as before
                        instr.lvar.varname = new_name
                    
                    self.variable_stacks[var_name].append(new_name)

        # Update phi functions in successors
        for succ in self.cfg.successors(block):
            if hasattr(succ, 'instrlist'):
                preds = list(self.cfg.predecessors(succ))
                if block in preds:
                    j = preds.index(block)

                    for instr, _ in succ.instrlist:
                        if isinstance(instr, ChironAST.PhiInstruction) and j < len(instr.source_vars):
                            var_name = self._get_base_name(instr.source_vars[j].varname)
                            if var_name in self.variable_stacks and self.variable_stacks[var_name]:
                                current_version = self.variable_stacks[var_name][-1]
                                old_name = instr.source_vars[j].varname
                                instr.source_vars[j].varname = current_version

        # Recurse on dominator tree children
        for child in sorted(self.dominator_tree.get(block, set()), 
                            key=lambda x: int(x.name) if x.name.isdigit() else float('inf')):
            self._rename_variables_in_block(child)

        # Restore variable stacks
        print(f"[Restore] Restoring variable_stacks after block {block.name}")
        self.variable_stacks = old_stacks

        # self._dump_all_blocks_instructions(f"After processing block {block.name}")

    def _rename_uses_in_instruction(self, instr):
        """
        Rename variable uses in an instruction based on current versions
        """
        # Handle assignment right-hand side
        if hasattr(instr, 'rexpr'):
            self._rename_uses_in_expression(instr.rexpr)

        # Handle conditions in ConditionCommand and AssertCommand
        if hasattr(instr, 'cond'):
            self._rename_uses_in_expression(instr.cond)

        # Handle movement expressions
        if hasattr(instr, 'expr'):
            self._rename_uses_in_expression(instr.expr)

        # Handle goto coordinates
        if hasattr(instr, 'xcor') and hasattr(instr, 'ycor'):
            self._rename_uses_in_expression(instr.xcor)
            self._rename_uses_in_expression(instr.ycor)


    def _rename_uses_in_expression(self, expr):
        """
        Rename variables in an expression based on current versions on the stack
        """
        if isinstance(expr, ChironAST.Var):
            var_name = self._get_base_name(expr.varname)
            if var_name in self.variable_stacks and self.variable_stacks[var_name]:
                current_version = self.variable_stacks[var_name][-1]
                old_name = expr.varname
                expr.varname = current_version
            else:
                print(f"      [Warning] No version for {var_name} — keeping as is")
        elif hasattr(expr, 'lexpr') and hasattr(expr, 'rexpr'):
            self._rename_uses_in_expression(expr.lexpr)
            self._rename_uses_in_expression(expr.rexpr)
        elif hasattr(expr, 'expr'):
            self._rename_uses_in_expression(expr.expr)