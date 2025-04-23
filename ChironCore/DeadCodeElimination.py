#!/usr/bin/python3
# -*- coding: utf-8 -*-
# Dead Code Elimination on SSA form for ChironLang

import os
import sys
import copy
import re
from collections import defaultdict, deque

# Import necessary Chiron modules
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from ChironAST import ChironAST

class DeadCodeElimination:
    def __init__(self, cfg):
        """
        Initialize the dead code elimination pass with a CFG in SSA form.
        
        Args:
            cfg: A control flow graph in SSA form
        """
        self.cfg = cfg
        self.variable_defs = {}    # Maps variables to their defining instructions
        self.variable_uses = defaultdict(set)  # Maps variables to instructions using them
        self.critical_instructions = set()  # Instructions with side effects or control flow
        self.live_instructions = set()      # Instructions that contribute to program output
        
    def eliminate_dead_code(self):
        """
        Main method to eliminate dead code from the CFG:
        1. Find all variable definitions and uses
        2. Identify critical instructions (those with side effects)
        3. Mark live instructions via backward propagation
        4. Remove dead instructions
        5. Remove empty loops
        
        Returns:
            The optimized CFG
        """
        print("\n===== DEAD CODE ELIMINATION STARTED =====")
        
        # Analyze variable definitions and uses
        self._analyze_variable_definitions_and_uses()
        
        # Identify critical instructions (with side effects or control flow)
        self._identify_critical_instructions()
        
        # Mark live instructions
        self._mark_live_instructions()
        
        # Remove dead instructions
        removed_count = self._remove_dead_instructions()
        print(f"Removed {removed_count} dead instructions")
        
        print("\n===== DEAD CODE ELIMINATION COMPLETED =====")
        
        return self.cfg
    
    def _analyze_variable_definitions_and_uses(self):
        """
        Build maps of variable definitions and uses throughout the program.
        """
        print("Analyzing variable definitions and uses...")
        
        # Process all blocks and their instructions
        for block in self.cfg.nodes():
            if not hasattr(block, 'instrlist') or not block.instrlist:
                continue
                
            for instr_idx, (instr, _) in enumerate(block.instrlist):
                # Store instruction location for easier reference
                instr_loc = (block, instr_idx)
                
                # Check for variable definitions
                if hasattr(instr, 'lvar') and isinstance(instr.lvar, ChironAST.Var):
                    var_name = instr.lvar.varname
                    self.variable_defs[var_name] = instr_loc
                
                # Check for phi function definitions
                if isinstance(instr, ChironAST.PhiInstruction):
                    target_var = instr.target_var.varname
                    self.variable_defs[target_var] = instr_loc
                    
                    # Record uses in phi functions
                    for source_var in instr.source_vars:
                        if isinstance(source_var, ChironAST.Var):
                            self.variable_uses[source_var.varname].add(instr_loc)
                
                # Record variable uses in expressions
                self._find_variable_uses_in_instruction(instr, instr_loc)
        
        var_def_count = len(self.variable_defs)
        var_use_count = sum(len(uses) for uses in self.variable_uses.values())
        print(f"Found {var_def_count} variable definitions and {var_use_count} variable uses")
    
    def _find_variable_uses_in_instruction(self, instr, instr_loc):
        """
        Find all variable uses in an instruction.
        
        Args:
            instr: The instruction to analyze
            instr_loc: Tuple of (block, instruction_index) for location reference
        """
        # Check for variable uses in assignment right-hand side
        if hasattr(instr, 'rexpr'):
            self._find_variable_uses_in_expression(instr.rexpr, instr_loc)
        
        # Check for variable uses in conditions
        if hasattr(instr, 'cond'):
            self._find_variable_uses_in_expression(instr.cond, instr_loc)
        
        # Check for variable uses in movement expressions
        if hasattr(instr, 'expr'):
            self._find_variable_uses_in_expression(instr.expr, instr_loc)
        
        # Check for variable uses in goto coordinates
        if hasattr(instr, 'xcor') and hasattr(instr, 'ycor'):
            self._find_variable_uses_in_expression(instr.xcor, instr_loc)
            self._find_variable_uses_in_expression(instr.ycor, instr_loc)
    
    def _find_variable_uses_in_expression(self, expr, instr_loc):
        """
        Recursively find all variable uses in an expression.
        
        Args:
            expr: The expression to analyze
            instr_loc: Tuple of (block, instruction_index) for location reference
        """
        if isinstance(expr, ChironAST.Var):
            self.variable_uses[expr.varname].add(instr_loc)
        elif hasattr(expr, 'lexpr') and hasattr(expr, 'rexpr'):
            self._find_variable_uses_in_expression(expr.lexpr, instr_loc)
            self._find_variable_uses_in_expression(expr.rexpr, instr_loc)
        elif hasattr(expr, 'expr'):
            self._find_variable_uses_in_expression(expr.expr, instr_loc)
    
    def _identify_critical_instructions(self):
        """
        Identify instructions that have side effects or affect control flow.
        These instructions cannot be eliminated regardless of liveness.
        """
        print("Identifying critical instructions...")
        
        # First, find all variables referenced in conditions
        control_vars = set()
        for block in self.cfg.nodes():
            if not hasattr(block, 'instrlist'):
                continue
                
            for instr_idx, (instr, _) in enumerate(block.instrlist):
                if isinstance(instr, ChironAST.ConditionCommand):
                    # Extract all variables from condition string representation
                    cond_str = str(instr)
                    for var_match in re.findall(r'(:[\w_]+)', cond_str):
                        control_vars.add(var_match)
        
        # Now identify critical instructions
        for block in self.cfg.nodes():
            if not hasattr(block, 'instrlist'):
                continue
                
            for instr_idx, (instr, _) in enumerate(block.instrlist):
                instr_loc = (block, instr_idx)
                
                # Control flow instructions are critical
                if isinstance(instr, ChironAST.ConditionCommand):
                    self.critical_instructions.add(instr_loc)
                
                # Side effect instructions are critical
                if (isinstance(instr, ChironAST.MoveCommand) or 
                    isinstance(instr, ChironAST.PenCommand) or 
                    isinstance(instr, ChironAST.GotoCommand)):
                    self.critical_instructions.add(instr_loc)
                    
                # Variable definitions used in control flow are critical
                if (isinstance(instr, ChironAST.AssignmentCommand) and 
                    hasattr(instr, 'lvar') and 
                    str(instr.lvar) in control_vars):
                    print(f"  Critical instruction (used in control flow): {instr}")
                    self.critical_instructions.add(instr_loc)
                    
                # Loop counter initializations are ALWAYS critical
                if (isinstance(instr, ChironAST.AssignmentCommand) and 
                    hasattr(instr, 'lvar') and 
                    ":__rep_counter_" in str(instr.lvar)):
                    print(f"  Critical instruction (loop counter): {instr}")
                    self.critical_instructions.add(instr_loc)
    
    def _mark_live_instructions(self):
        """
        Mark instructions as live through backward propagation.
        Start from critical instructions and mark all instructions
        that contribute to them as live.
        """
        print("Marking live instructions...")
        
        # Initialize worklist with critical instructions
        worklist = deque(self.critical_instructions)
        
        # Mark all instructions in the worklist as live
        while worklist:
            instr_loc = worklist.popleft()
            
            # Skip if already processed
            if instr_loc in self.live_instructions:
                continue
            
            # Mark as live
            self.live_instructions.add(instr_loc)
            
            # Get the instruction
            block, instr_idx = instr_loc
            instr, _ = block.instrlist[instr_idx]
            
            # For each variable used in this instruction, add its definition to the worklist
            used_vars = self._get_variables_used_in_instruction(instr)
            
            for var_name in used_vars:
                if var_name in self.variable_defs:
                    def_loc = self.variable_defs[var_name]
                    if def_loc not in self.live_instructions:
                        worklist.append(def_loc)
        
        print(f"Marked {len(self.live_instructions)} instructions as live")
    
    def _get_variables_used_in_instruction(self, instr):
        """
        Get all variables used in an instruction.
        
        Args:
            instr: The instruction to analyze
            
        Returns:
            A set of variable names used in the instruction
        """
        used_vars = set()
        
        # Check for variable uses in assignment right-hand side
        if hasattr(instr, 'rexpr'):
            self._get_variables_used_in_expression(instr.rexpr, used_vars)
        
        # Check for variable uses in conditions
        if hasattr(instr, 'cond'):
            self._get_variables_used_in_expression(instr.cond, used_vars)
        
        # Check for variable uses in movement expressions
        if hasattr(instr, 'expr'):
            self._get_variables_used_in_expression(instr.expr, used_vars)
        
        # Check for variable uses in goto coordinates
        if hasattr(instr, 'xcor') and hasattr(instr, 'ycor'):
            self._get_variables_used_in_expression(instr.xcor, used_vars)
            self._get_variables_used_in_expression(instr.ycor, used_vars)
        
        # Check for variable uses in phi functions
        if isinstance(instr, ChironAST.PhiInstruction):
            for source_var in instr.source_vars:
                if isinstance(source_var, ChironAST.Var):
                    used_vars.add(source_var.varname)
        
        return used_vars
    
    def _get_variables_used_in_expression(self, expr, used_vars):
        """
        Recursively find all variables used in an expression.
        
        Args:
            expr: The expression to analyze
            used_vars: Set to add variable names to
        """
        if isinstance(expr, ChironAST.Var):
            used_vars.add(expr.varname)
        elif hasattr(expr, 'lexpr') and hasattr(expr, 'rexpr'):
            self._get_variables_used_in_expression(expr.lexpr, used_vars)
            self._get_variables_used_in_expression(expr.rexpr, used_vars)
        elif hasattr(expr, 'expr'):
            self._get_variables_used_in_expression(expr.expr, used_vars)
    
    def _remove_dead_instructions(self):
        """
        Remove instructions that are not marked as live.
        
        Returns:
            Number of instructions removed
        """
        print("Removing dead instructions...")
        
        removed_count = 0
        
        for block in self.cfg.nodes():
            if not hasattr(block, 'instrlist') or not block.instrlist:
                continue
            
            # Create a new instruction list with only live instructions
            new_instrlist = []
            
            for instr_idx, (instr, line_num) in enumerate(block.instrlist):
                instr_loc = (block, instr_idx)
                
                if instr_loc in self.live_instructions:
                    # Keep live instructions
                    new_instrlist.append((instr, line_num))
                else:
                    # For dead instructions, check if they're safe to remove
                    can_remove = True
                    
                    # Keep phi functions for now (they'll be handled by SSA destruction)
                    if isinstance(instr, ChironAST.PhiInstruction):
                        new_instrlist.append((instr, line_num))
                        continue
                    
                    # Don't remove instructions with side effects
                    if (isinstance(instr, ChironAST.MoveCommand) or 
                        isinstance(instr, ChironAST.PenCommand) or 
                        isinstance(instr, ChironAST.GotoCommand) or
                        isinstance(instr, ChironAST.ConditionCommand)):
                        new_instrlist.append((instr, line_num))
                        continue
                    
                    # For other instructions, replace with NOP
                    if can_remove:
                        new_instrlist.append((ChironAST.NoOpCommand(), line_num))
                        removed_count += 1
                        print(f"  Removed dead instruction at block {block.name}, index {instr_idx}: {instr}")
            
            # Update the block's instruction list
            block.instrlist = new_instrlist
        
        return removed_count

    