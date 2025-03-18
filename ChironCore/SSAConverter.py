#!/usr/bin/python3
# -*- coding: utf-8 -*-
# Corrected SSA Converter for ChironLang

import os
import sys
import copy
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
        3. Place phi functions at appropriate merge points
        4. Rename variables to their SSA versions
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
    
    def _find_all_variables(self):
        """
        Find all variables and their definitions in the program.
        This ensures we have entries for all variables before doing anything else.
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
        Get the base name of a variable (without SSA suffix).
        """
        if "_" in var_name:
            parts = var_name.split("_")
            if len(parts) > 1 and parts[-1].isdigit():
                return "_".join(parts[:-1])
        return var_name
    
    def _collect_variables_from_instruction(self, instr):
        """
        Collect all variables used in an instruction.
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
        Recursively collect all variables from an expression.
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
            
            # Compute dominators - this is needed for dominance frontiers
            self.dominators = {}
            for node in G.nodes():
                self.dominators[node] = set()
                current = node
                while current is not None and current != entry_block:
                    if current in self.immediate_dominators:
                        dom = self.immediate_dominators[current]
                        if dom != current:  # Exclude the node itself
                            self.dominators[node].add(dom)
                        current = dom
                    else:
                        break
                # Always add entry_block for all nodes except itself
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
            print("Successfully computed dominance frontiers")
        except Exception as e:
            print(f"Error in dominance frontier calculation: {e}")
    
    def _compute_dominance_frontiers(self):
        """
        Compute the dominance frontier for each block.
        The dominance frontier of a block B is the set of all blocks where B's dominance ends.
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
        for block in self.cfg.nodes():
            # For each child in the dominator tree
            for dom_child in self.dominator_tree.get(block, set()):
                # For each block in the child's dominance frontier
                for frontier_block in self.dominance_frontier.get(dom_child, set()):
                    # If the current block doesn't strictly dominate the frontier block
                    if self.immediate_dominators.get(frontier_block) != block:
                        # Add the frontier block to the current block's dominance frontier
                        self.dominance_frontier[block].add(frontier_block)
    
    def _place_phi_functions(self):
        """
        Place phi functions at the heads of basic blocks where variables merge.
        We place a phi function for a variable at each block in its iterated
        dominance frontier.
        """
        print("\n===== PLACING PHI FUNCTIONS =====")
        
        # Count of phi functions placed
        phi_count = 0
        
        # For each variable that is defined in multiple blocks
        for var_name, def_blocks in self.variable_defs.items():
            if len(def_blocks) <= 1:
                continue  # No need for phi functions
            
            print(f"Processing variable: {var_name}")
            
            # Track blocks where we've placed phi functions for this variable
            phi_blocks = set()
            
            # Use a worklist algorithm to place phi functions in the
            # iterated dominance frontier
            worklist = list(def_blocks)
            while worklist:
                block = worklist.pop()
                
                # For each block in the dominance frontier of this block
                for df_block in self.dominance_frontier.get(block, set()):
                    # If we haven't already placed a phi function here
                    if df_block not in phi_blocks:
                        print(f"  Placing phi function for {var_name} in block {df_block.name}")
                        
                        # Create the phi function
                        target_var = ChironAST.Var(var_name)
                        source_vars = []
                        source_blocks = []
                        
                        # Add a source for each predecessor
                        for pred in self.cfg.predecessors(df_block):
                            source_vars.append(ChironAST.Var(var_name))
                            source_blocks.append(pred)
                        
                        # Create the phi instruction
                        phi = ChironAST.PhiInstruction(target_var, source_vars, source_blocks)
                        
                        # Insert at the beginning of the block with PC increment of 0
                        # This is the key change - using 0 instead of -1
                        df_block.instrlist.insert(0, (phi, 0))
                        
                        # Mark that we've placed a phi function here
                        phi_blocks.add(df_block)
                        phi_count += 1
                        
                        # If this block doesn't already define this variable,
                        # we now need to consider it for placing more phi functions
                        if df_block not in self.variable_defs[var_name]:
                            self.variable_defs[var_name].add(df_block)
                            worklist.append(df_block)
        
        print(f"Total phi functions placed: {phi_count}")
    
    def _rename_variables(self):
        """
        Rename variables to their SSA versions:
        1. Initialize stacks for each variable
        2. Process blocks in a non-recursive depth-first traversal
        3. Update variable uses and definitions
        """
        print("\n===== RENAMING VARIABLES =====")
        
        # Initialize stacks for each variable
        self.variable_stacks = {var: [] for var in self.all_variables}
        
        # Find the entry block
        entry_block = None
        for block in self.cfg.nodes():
            if block.name == "START" or self.cfg.in_degree(block) == 0:
                entry_block = block
                break
        
        if not entry_block:
            print("ERROR: No entry block found in CFG")
            return
        
        # Process blocks in dominance tree order
        self._rename_variables_in_subtree(entry_block)
    
    def _rename_variables_in_subtree(self, block):
        """
        Rename variables in a subtree of the dominator tree.
        This is a recursive implementation that maintains proper scoping.
        """
        if not hasattr(block, 'instrlist'):
            return
            
        print(f"Renaming variables in block: {block.name}")
        
        # Save old variable stacks to restore later
        old_stacks = {var: list(stack) for var, stack in self.variable_stacks.items()}
        
        # First, process phi functions at the beginning of the block
        for i, (instr, _) in enumerate(block.instrlist):
            if isinstance(instr, ChironAST.PhiInstruction):
                # Get the original variable name
                var_name = self._get_base_name(instr.target_var.varname)
                
                # Create a new version
                new_version = self.variable_versions.get(var_name, 0) + 1
                self.variable_versions[var_name] = new_version
                
                # Create the SSA name
                new_name = f"{var_name}_{new_version}"
                
                # Update the target variable
                instr.target_var.varname = new_name
                
                # Push the new version onto the stack
                self.variable_stacks[var_name].append(new_name)
                
                print(f"  Renamed phi target: {var_name} -> {new_name}")
        
        # Then, process all other instructions
        for i, (instr, _) in enumerate(block.instrlist):
            # Skip phi instructions (already processed)
            if isinstance(instr, ChironAST.PhiInstruction):
                continue
            
            # Process uses (right-hand side)
            self._rename_uses_in_instruction(instr)
            
            # Process definitions (left-hand side)
            if hasattr(instr, 'lvar') and isinstance(instr.lvar, ChironAST.Var):
                var_name = self._get_base_name(instr.lvar.varname)
                
                # Create a new version
                new_version = self.variable_versions.get(var_name, 0) + 1
                self.variable_versions[var_name] = new_version
                
                # Create the SSA name
                new_name = f"{var_name}_{new_version}"
                
                # Update the variable
                instr.lvar.varname = new_name
                
                # Push the new version onto the stack
                self.variable_stacks[var_name].append(new_name)
                
                print(f"  Renamed definition: {var_name} -> {new_name}")
        
        # Process successor phi functions
        for succ in self.cfg.successors(block):
            # Update phi functions in this successor
            for instr, _ in succ.instrlist:
                if isinstance(instr, ChironAST.PhiInstruction):
                    # Find the position of this block in the phi's sources
                    for i, source_block in enumerate(instr.source_blocks):
                        if source_block == block:
                            # Get the base name of the variable
                            var_name = self._get_base_name(instr.source_vars[i].varname)
                            
                            # Get the current version from the stack
                            if var_name in self.variable_stacks and self.variable_stacks[var_name]:
                                current_version = self.variable_stacks[var_name][-1]
                                instr.source_vars[i].varname = current_version
                                print(f"  Updated phi source in {succ.name}: {var_name} -> {current_version}")
                            else:
                                # If there's no current version, use a version 0
                                new_name = f"{var_name}_0"
                                instr.source_vars[i].varname = new_name
                                print(f"  Updated phi source in {succ.name} with initialized value: {var_name} -> {new_name}")
        
        # Recursively process all children in the dominator tree
        for child in self.dominator_tree.get(block, set()):
            self._rename_variables_in_subtree(child)
        
        # Restore variable stacks to their state before processing this block
        # This is important for maintaining proper scoping when returning from recursion
        self.variable_stacks = old_stacks
    
    def _rename_uses_in_instruction(self, instr):
        """
        Rename variable uses in an instruction based on current versions.
        """
        # Assignment right-hand side
        if hasattr(instr, 'rexpr'):
            self._rename_uses_in_expression(instr.rexpr)
        
        # Condition
        if hasattr(instr, 'cond'):
            self._rename_uses_in_expression(instr.cond)
        
        # Move expression
        if hasattr(instr, 'expr'):
            self._rename_uses_in_expression(instr.expr)
        
        # Goto coordinates
        if hasattr(instr, 'xcor') and hasattr(instr, 'ycor'):
            self._rename_uses_in_expression(instr.xcor)
            self._rename_uses_in_expression(instr.ycor)
    
    def _rename_uses_in_expression(self, expr):
        """
        Rename variables in an expression based on current versions.
        """
        if isinstance(expr, ChironAST.Var):
            var_name = self._get_base_name(expr.varname)
            
            # Get the current version from the stack
            if var_name in self.variable_stacks and self.variable_stacks[var_name]:
                current_version = self.variable_stacks[var_name][-1]
                expr.varname = current_version
                print(f"  Renamed use: {var_name} -> {current_version}")
            else:
                # Initialize with version 0 for undefined variables
                new_name = f"{var_name}_0"
                expr.varname = new_name
                self.variable_stacks[var_name].append(new_name)
                print(f"  Initialized undefined variable: {var_name} -> {new_name}")
        
        # Recursively process sub-expressions
        elif hasattr(expr, 'lexpr') and hasattr(expr, 'rexpr'):
            self._rename_uses_in_expression(expr.lexpr)
            self._rename_uses_in_expression(expr.rexpr)
        elif hasattr(expr, 'expr'):
            self._rename_uses_in_expression(expr.expr)