#!/usr/bin/python3
# -*- coding: utf-8 -*-
# Corrected SSA Destroyer for ChironLang

import os
import sys
import re
import copy
from collections import defaultdict

# Import necessary Chiron modules
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from ChironAST import ChironAST

class SSADestroyer:
    def __init__(self, cfg):
        self.cfg = cfg
        self.variable_map = {}  # Maps SSA variables to base names
        self.phi_functions = [] # List of (block, index, phi) tuples
        self.copy_operations = [] # List of (block, index, source, target) tuples
        
        # Store original variable names (before SSA)
        self.original_vars = set()
    
    def convert_from_ssa(self):
        """
        Convert the CFG from SSA form back to normal form:
        1. Collect phi function information
        2. Generate copy operations to replace phi functions
        3. Remove phi functions
        4. Rename all variables back to their base names
        """
        print("\n===== SSA DESTRUCTION STARTED =====")
        
        # Identify original variables (those that exist before SSA conversion)
        self._identify_original_variables()
        
        # Build a mapping of all variables to their base names
        self._build_variable_map()
        
        # Collect all phi functions
        self._collect_phi_functions()
        
        # Generate copy operations to replace phi functions
        self._generate_copy_operations()
        
        # Insert the copy operations into the CFG
        self._insert_copy_operations()
        
        # Remove all phi functions
        phi_count = self._remove_phi_functions()
        print(f"Replaced {phi_count} phi functions with copy operations")
        
        # Rename all variables back to their base names
        renamed_count = self._rename_variables()
        print(f"Removed SSA suffixes from {renamed_count} variables")
        
        # Clean up redundant self-assignments
        removed_count = self._remove_redundant_assignments()
        print(f"Removed {removed_count} redundant self-assignments")
        
        print("\n===== SSA DESTRUCTION COMPLETED =====")
        
        return self.cfg
    
    def _identify_original_variables(self):
        """
        Identify variables that existed before SSA conversion
        by looking for variables without SSA suffix pattern.
        """
        for block in self.cfg.nodes():
            if hasattr(block, 'instrlist'):
                for instr, _ in block.instrlist:
                    self._scan_instruction_for_original_vars(instr)
    
    def _scan_instruction_for_original_vars(self, instr):
        """
        Scan an instruction to identify potential original variables
        """
        # Consider non-SSA-versioned variables as original
        if hasattr(instr, 'lvar') and isinstance(instr.lvar, ChironAST.Var):
            var_name = instr.lvar.varname
            if not re.match(r'.+_\d+$', var_name):
                self.original_vars.add(var_name)
        
        # Process expressions
        if hasattr(instr, 'rexpr'):
            self._scan_expression_for_original_vars(instr.rexpr)
        
        if hasattr(instr, 'cond'):
            self._scan_expression_for_original_vars(instr.cond)
        
        if hasattr(instr, 'expr'):
            self._scan_expression_for_original_vars(instr.expr)
        
        if hasattr(instr, 'xcor') and hasattr(instr, 'ycor'):
            self._scan_expression_for_original_vars(instr.xcor)
            self._scan_expression_for_original_vars(instr.ycor)
    
    def _scan_expression_for_original_vars(self, expr):
        """
        Scan an expression to identify potential original variables
        """
        if isinstance(expr, ChironAST.Var):
            var_name = expr.varname
            if not re.match(r'.+_\d+$', var_name):
                self.original_vars.add(var_name)
        elif hasattr(expr, 'lexpr') and hasattr(expr, 'rexpr'):
            self._scan_expression_for_original_vars(expr.lexpr)
            self._scan_expression_for_original_vars(expr.rexpr)
        elif hasattr(expr, 'expr'):
            self._scan_expression_for_original_vars(expr.expr)
    
    def _build_variable_map(self):
        """
        Build a mapping of all SSA variables to their base names
        """
        for block in self.cfg.nodes():
            if hasattr(block, 'instrlist'):
                for instr, _ in block.instrlist:
                    self._process_instruction_for_variables(instr)
        
        # Mark known original variables in the map
        for var in self.original_vars:
            if var in self.variable_map:
                # Keep the original name intact
                self.variable_map[var] = var
    
    def _process_instruction_for_variables(self, instr):
        """
        Process an instruction to identify SSA variables and their base names
        """
        # Process phi instruction
        if isinstance(instr, ChironAST.PhiInstruction):
            target = instr.target_var.varname
            base_name = self._get_base_name(target)
            self.variable_map[target] = base_name
            
            for source_var in instr.source_vars:
                if isinstance(source_var, ChironAST.Var):
                    source = source_var.varname
                    self.variable_map[source] = self._get_base_name(source)
                    
            return
        
        # Process assignment left-hand side
        if hasattr(instr, 'lvar') and isinstance(instr.lvar, ChironAST.Var):
            var_name = instr.lvar.varname
            self.variable_map[var_name] = self._get_base_name(var_name)
        
        # Process expressions
        if hasattr(instr, 'rexpr'):
            self._process_expression_for_variables(instr.rexpr)
        
        if hasattr(instr, 'cond'):
            self._process_expression_for_variables(instr.cond)
        
        if hasattr(instr, 'expr'):
            self._process_expression_for_variables(instr.expr)
        
        if hasattr(instr, 'xcor') and hasattr(instr, 'ycor'):
            self._process_expression_for_variables(instr.xcor)
            self._process_expression_for_variables(instr.ycor)
    
    def _process_expression_for_variables(self, expr):
        """
        Process an expression to identify SSA variables and their base names
        """
        if isinstance(expr, ChironAST.Var):
            var_name = expr.varname
            self.variable_map[var_name] = self._get_base_name(var_name)
        elif hasattr(expr, 'lexpr') and hasattr(expr, 'rexpr'):
            self._process_expression_for_variables(expr.lexpr)
            self._process_expression_for_variables(expr.rexpr)
        elif hasattr(expr, 'expr'):
            self._process_expression_for_variables(expr.expr)
    
    def _get_base_name(self, var_name):
        """
        Get the base name of a variable (without SSA suffix)
        """
        # Special case for loop counter variables
        if ":__rep_counter_" in var_name:
            # Extract the counter number but keep it as part of the base name
            # E.g., ":__rep_counter_1_2" should become ":__rep_counter_1"
            match = re.match(r'(:__rep_counter_\d+)(_\d+)?$', var_name)
            if match:
                return match.group(1)  # Return with counter number intact
        
        # Regular SSA variables
        match = re.match(r'(.+)_\d+$', var_name)
        if match:
            return match.group(1)
        
        return var_name
    
    def _collect_phi_functions(self):
        """
        Collect all phi functions in the CFG
        """
        for block in self.cfg.nodes():
            if hasattr(block, 'instrlist'):
                for i, (instr, pc) in enumerate(block.instrlist):
                    if isinstance(instr, ChironAST.PhiInstruction):
                        self.phi_functions.append((block, i, instr))
    
    def _generate_copy_operations(self):
        """
        Generate copy operations to replace phi functions
        """
        for block, idx, phi in self.phi_functions:
            target_var = phi.target_var.varname
            
            # For each source of the phi function
            for source_var, pred_block in zip(phi.source_vars, phi.source_blocks):
                if not isinstance(source_var, ChironAST.Var):
                    continue
                
                source_name = source_var.varname
                
                # Skip self-assignments
                if source_name == target_var:
                    continue
                
                # Create a copy operation: target = source
                copy_op = ChironAST.AssignmentCommand(
                    ChironAST.Var(target_var),  # Keep the SSA name for now
                    ChironAST.Var(source_name)  # Keep the SSA name for now
                )
                
                # Find the right position in the predecessor block
                pos = len(pred_block.instrlist)
                # Insert before any branch instruction
                for j in range(len(pred_block.instrlist) - 1, -1, -1):
                    if isinstance(pred_block.instrlist[j][0], ChironAST.ConditionCommand):
                        pos = j
                        break
                
                self.copy_operations.append((pred_block, pos, copy_op))
    
    def _insert_copy_operations(self):
        """
        Insert copy operations into the CFG
        """
        # Sort by block name and position to maintain stability
        self.copy_operations.sort(key=lambda x: (x[0].name, x[1]))
        
        # Track offset for each block (to account for multiple insertions)
        offsets = defaultdict(int)
        
        # Insert copy operations
        for block, pos, copy_op in self.copy_operations:
            adjusted_pos = pos + offsets[block.name]
            block.instrlist.insert(adjusted_pos, (copy_op, 1))  # Using PC increment of 1
            offsets[block.name] += 1
    
    def _remove_phi_functions(self):
        """
        Remove all phi functions from the CFG while updating line numbers
        """
        phi_count = len(self.phi_functions)
        
        # Sort phi functions by block name and position
        sorted_phis = sorted(self.phi_functions, key=lambda x: (x[0].name, x[1]), reverse=True)
        
        # Remove phi functions and update line numbers
        for block, idx, phi in sorted_phis:
            # Get the line number of the phi function
            _, phi_line = block.instrlist[idx]
            
            # Remove the phi function
            del block.instrlist[idx]
            
            # Update line numbers for instructions that should take their place
            for i in range(idx, len(block.instrlist)):
                instr, line = block.instrlist[i]
                if line > phi_line:
                    # Shift line numbers down to fill the gap
                    block.instrlist[i] = (instr, line - 1)
        
        return phi_count
    
    def _rename_variables(self):
        """
        Rename all variables back to their base names
        """
        renamed_count = 0
        
        for block in self.cfg.nodes():
            if hasattr(block, 'instrlist'):
                for instr, _ in block.instrlist:
                    renamed_count += self._rename_vars_in_instruction(instr)
        
        return renamed_count
    
    def _rename_vars_in_instruction(self, instr):
        """
        Rename variables in an instruction back to their base names
        """
        count = 0
        
        # Handle assignment target
        if hasattr(instr, 'lvar') and isinstance(instr.lvar, ChironAST.Var):
            if self._rename_var(instr.lvar):
                count += 1
        
        # Handle assignment expression
        if hasattr(instr, 'rexpr'):
            count += self._rename_vars_in_expression(instr.rexpr)
        
        # Handle condition
        if hasattr(instr, 'cond'):
            count += self._rename_vars_in_expression(instr.cond)
        
        # Handle move expression
        if hasattr(instr, 'expr'):
            count += self._rename_vars_in_expression(instr.expr)
        
        # Handle goto coordinates
        if hasattr(instr, 'xcor') and hasattr(instr, 'ycor'):
            count += self._rename_vars_in_expression(instr.xcor)
            count += self._rename_vars_in_expression(instr.ycor)
        
        return count
    
    def _rename_vars_in_expression(self, expr):
        """
        Rename variables in an expression back to their base names
        """
        count = 0
        
        if isinstance(expr, ChironAST.Var):
            if self._rename_var(expr):
                count += 1
        elif hasattr(expr, 'lexpr') and hasattr(expr, 'rexpr'):
            count += self._rename_vars_in_expression(expr.lexpr)
            count += self._rename_vars_in_expression(expr.rexpr)
        elif hasattr(expr, 'expr'):
            count += self._rename_vars_in_expression(expr.expr)
        
        return count
    
    def _rename_var(self, var):
        """
        Rename a variable back to its base name
        """
        original = var.varname
        
        if original in self.variable_map:
            base_name = self.variable_map[original]
            if original != base_name:
                var.varname = base_name
                print(f"Renamed: {original} -> {base_name}")
                return True
        
        return False
    
    def _remove_redundant_assignments(self):
        """
        Remove redundant self-assignments like x = x
        """
        removed_count = 0
        
        for block in self.cfg.nodes():
            if not hasattr(block, 'instrlist'):
                continue
                
            # Use a new list to collect non-redundant instructions
            new_instrlist = []
            
            for instr, pc in block.instrlist:
                # Check if this is a self-assignment
                if (isinstance(instr, ChironAST.AssignmentCommand) and 
                    hasattr(instr, 'lvar') and hasattr(instr, 'rexpr') and
                    isinstance(instr.lvar, ChironAST.Var) and isinstance(instr.rexpr, ChironAST.Var) and
                    instr.lvar.varname == instr.rexpr.varname):
                    # Skip this redundant assignment
                    print(f"Removing redundant assignment: {instr.lvar.varname} = {instr.rexpr.varname}")
                    removed_count += 1
                else:
                    # Keep this instruction
                    new_instrlist.append((instr, pc))
            
            # Replace with the filtered list
            block.instrlist = new_instrlist
        
        return removed_count