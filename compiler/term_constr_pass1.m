%-----------------------------------------------------------------------------%
% Copyright (C) 1995-1998 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% file: term_constr_pass1.m
% main author: vjteag


% Implements a fixpoint algorithm (as in Benoy and King: "Inferring 
% Argument size relationships with CLP(R)") to find constraints on
% argument sizes.

:- module term_constr_pass1.

:- interface.

:- import_module list, hlds_module, hlds_pred, term_util.

% Need enough info to make traversal params.
:- pred find_arg_sizes_in_scc(list(pred_proc_id), module_info, size_varset, 
		pass_info, widening_info, module_info, size_varset, 
							io__state, io__state).  
:- mode find_arg_sizes_in_scc(in, in, in, in, in, out, out, di, uo) is det.

:- type widening_info
	--->	
		remove_parallel_constraints	% Widen by removing any
						% constraints in the current
						% iteration's constraint set
						% for which there was a
						% parallel but stronger
						% equation in the previous
						% iteration.
							
	;
		widen_after_fixed_iterations(int)
						% Widen using the algorithm in
						% the Benoy & King paper:
						% After some fixed number of
						% iterations, remove all the
						% constraints in the old (i.e.
						% previous iteration's) set of
						% constraints that are not
						% implied by the new set of
						% constraints.
	.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module bimap, bool, hlds_goal, hlds_module, hlds_pred, int, io, list, 
	lp_rational, map, prog_data, quantification, rat, require, set, 
	std_util, term, varset, term_constr_traversal, term_util.

%-----------------------------------------------------------------------------%

find_arg_sizes_in_scc(SCC, Module_info0, SizeVars0, Pass_info, Widen_info, 
		Module_info, SizeVars) -->
	find_arg_sizes_in_scc2(SCC, Module_info0, SizeVars0, Pass_info, 
			Widen_info, 0, Module_info, SizeVars).
 
:- pred find_arg_sizes_in_scc2(list(pred_proc_id), module_info, size_varset, 
		pass_info, widening_info, int, module_info, size_varset, 
		io__state, io__state).
:- mode find_arg_sizes_in_scc2(in, in, in, in, in, in, out, out, di, uo) is det.

find_arg_sizes_in_scc2(SCC, Module_info0, SizeVars0, Pass_info, Widen_info, 
		It_num, Module_info, SizeVars, IO0, IO) :-
	Pass_info = pass_info(Func_info, _, _), 
			%XXX Should use info about max errors to collect?
	do_one_iteration(SCC, Module_info0, SizeVars0, Func_info, Widen_info, 
		It_num, Module_info1, SizeVars1, Change_flag, IO0, IO1),	

	% Change_flag is "yes" iff the constraints have changed since the
	% previous iteration.  Otherwise, we have reached a fixpoint.
	( Change_flag = yes ->
		Next_it_num = It_num + 1,
		find_arg_sizes_in_scc2(SCC, Module_info1, SizeVars1, Pass_info,
			Widen_info, Next_it_num, Module_info, SizeVars, IO1, IO)
	;
		Module_info = Module_info1,
		IO = IO1,
		SizeVars = SizeVars1
	).

% do_one_iteration:
% Calculates the next approximation to the argument-size constraints
% Change_flag is "yes" iff the constraints for any procedure in the SCC have
% changed since the last iteration.
:- pred do_one_iteration(list(pred_proc_id), module_info, size_varset, 
		functor_info, widening_info, int, module_info, size_varset,
		bool, io__state, io__state).
:- mode do_one_iteration(in, in, in, in, in, in, out, out, out,
		di, uo) is det.

do_one_iteration([], Mod_info, SizeVars, _, _, _, Mod_info, SizeVars, no, 
									IO, IO).
do_one_iteration([PPID|SCC], Mod_info0, SizeVars0, Func_info, Wid_info, It_num, 
		Mod_info, SizeVars, Change_flag, IO0, IO) :-
	find_constraints_pred(PPID, Mod_info0, SizeVars0, Func_info, Wid_info, 
		It_num, Mod_info1, SizeVars1, PPID_Change_flag, IO0, IO1),

	do_one_iteration(SCC, Mod_info1, SizeVars1, Func_info, Wid_info, It_num,
		Mod_info, SizeVars, SCC_Change_flag, IO1, IO),
	( (PPID_Change_flag = yes ; SCC_Change_flag = yes) ->
		Change_flag = yes
	;
		Change_flag = no
	).
	

% Find next approximation to the constraints for a single predicate, which 
% may be part of a larger SCC.
:- pred find_constraints_pred(pred_proc_id, module_info, size_varset, 
		functor_info, widening_info, int, module_info, size_varset, 
		bool, io__state, io__state).
:- mode find_constraints_pred(in, in, in, in, in, in, out, out, out, 
		di, uo) is det.
	
find_constraints_pred(PPID, Module_info0, SizeVars0, Func_info, Widening_info, 
		It_num, Module_info, SizeVars, Change_flag, IO0,IO):- 

	PPID = proc(PredId, ProcId),
	module_info_pred_proc_info(Module_info0, PredId, ProcId, PredInfo, 
								ProcInfo),
	pred_info_context(PredInfo, Context),
	proc_info_vartypes(ProcInfo, VarTypes),
	proc_info_goal(ProcInfo, Goal),

	lookup_proc_arg_size_info(Module_info0, PPID, Maybe_arg_size_info),

	(	Maybe_arg_size_info = no, 
		( It_num = 0 ->
			% If this is the first iteration, initialise the data
			% structures required for traversal of this predicate.
			fill_var_to_sizevar_map(Goal, SizeVars0, SizeVars1, 
							VarToSizeVarMap),

			find_zero_size_vars(Module_info0, VarToSizeVarMap,
						VarTypes, Zeros),

			term_constr_traversal__init_traversal_params(
				Module_info0, Func_info, PPID, Context, 
				VarTypes, Zeros, VarToSizeVarMap, 
							Traversal_params),

			do_traversal(Goal, Traversal_params, SizeVars1,
				constr_info(SizeVars, Constraint_info), 
								IO0, IO),

			( 	Constraint_info = eqns(Constraints), 
				update_arg_size_info(PPID, Constraints, Zeros, 
				VarToSizeVarMap, Module_info0, Module_info),
				Change_flag = yes
			;
				% If we get no constraints, set the
				% arg_size_info to yes(constraints([])) to
				% indicate that we have traversed this
				% predicate but haven't found anything.
				Constraint_info = false_equation,
				update_arg_size_info(PPID, [], Zeros, 
					VarToSizeVarMap, Module_info0, 
					Module_info),
				Change_flag = no
			)
		;
			error("term_constr_pass1: not the first iteration but 
						no arg size info")
		) 
	;
		Maybe_arg_size_info = yes(finite(_,_)),
		error("term_constr_pass1: wrong type of argument size info\n")
	;
		Maybe_arg_size_info = yes(infinite(_)),
		error("term_constr_pass1: wrong type of argument size info\n")
	;
		Maybe_arg_size_info = yes(constraints(Old_constraints, 
						Zeros, VarToSizeVarMap)),

		% If we have already traversed this predicate, traverse it
		% again and compare the new equations with the old.  If they
		% are the same, this may be a fixpoint so set Change_flag to
		% "no".  If they are different, set the Change_flag to "yes".

		% We need to pass the old variable map to do_traversal 
		% because then the variables in the two sets of constraints 
		% will have the same correspondence to the variables in the
		% procedure.
		term_constr_traversal__init_traversal_params(Module_info0, 
			Func_info, PPID, Context, VarTypes, Zeros, 
					VarToSizeVarMap, Traversal_params),

		do_traversal(Goal, Traversal_params, SizeVars0, 
			constr_info(SizeVars, Unwidened_Constraint_info),
					IO0, IO1),
		
		( 	Unwidened_Constraint_info = false_equation,
			( Old_constraints = [] ->
				Change_flag = no,
				Module_info = Module_info0,
				IO = IO1
			;
				error("term_constr_pass1: New equations not
				implied by old")
			)
		;
			Unwidened_Constraint_info = eqns(Unwidened_Constraints),
			write("Testing fixpoint: Iteration ", IO1, IO2),
			write(It_num, IO2, IO),
			test_fixpoint_and_perhaps_widen(Widening_info, SizeVars,
				It_num, Unwidened_Constraints, 
					Old_constraints, Constraints, 
								Change_flag),
			update_arg_size_info(PPID, Constraints, Zeros, 
				VarToSizeVarMap, Module_info0, Module_info)
		)
	).


:- pred update_arg_size_info(pred_proc_id, equations, set(size_var), 
		bimap(prog_var, size_var), module_info, module_info).
:- mode update_arg_size_info(in, in, in, in, in, out) is det.

update_arg_size_info(PPID, Constraints, Zeros, VarMap, Mod_info0, Mod_info) :-
	canonical_form(Constraints, Canonical_constraints),
	list__sort(compare_eqns, Canonical_constraints, Sorted_constraints), 	
	set_pred_proc_ids_arg_size_info([PPID], 
		constraints(Sorted_constraints, Zeros, VarMap), Mod_info0, 
								Mod_info). 


% test_fixpoint_and_perhaps_widen(Widening_info, Vars, _, 
%		Unwidened_eqns0, Old_eqns, Widened_eqns, Changed_flag):
%  
% This assumes that constraints already entered in module info (i.e. the
% old equations) are in canonical form and are sorted.
% It outputs a list of equations that are in canonical form and are sorted.
:- pred test_fixpoint_and_perhaps_widen(widening_info, size_varset, int, 
				equations, equations, equations, bool).
:- mode test_fixpoint_and_perhaps_widen(in, in, in, in, in, out, out) is det.

test_fixpoint_and_perhaps_widen(remove_parallel_constraints, Vars, _, 
		Unwidened_eqns0, Old_eqns, Widened_eqns, Changed_flag) :- 

	remove_redundant_eqns(Unwidened_eqns0, Unwidened_eqns),

	No_stronger_parallel_constraints = lambda( [Eqn::in] is semidet, (
		no_stronger_parallel_constraints(Eqn, Old_eqns)
	)),

	% Keep only those constraints for which there are no stronger 
	% parallel constraints occuring in the old equations.
	list__filter(No_stronger_parallel_constraints, Unwidened_eqns,
								Widened_eqns0),

	canonical_form(Widened_eqns0, Widened_eqns1),
	list__sort(compare_eqns, Widened_eqns1, Widened_eqns), 	

	test_fixpoint(Widened_eqns, Old_eqns, Vars, Changed_flag).


test_fixpoint_and_perhaps_widen(widen_after_fixed_iterations(Num), Vars, It_num,
		New_eqns, Old_eqns, Widened_eqns, Changed_flag) :-

	% This test should be unnecessary if the algorithm is implemented
	% correctly.  Worth leaving in for now, though.
	Entailed_by_old = lambda([Eqn::in] is semidet, (
		entailed(Eqn, Old_eqns, Vars)
	)),
	list__filter(Entailed_by_old, New_eqns, Weaker_eqns),
	( \+ ( list__same_length(New_eqns, Weaker_eqns) ; It_num = 0) ->
		error("term_constr_pass1: New equations not entailed by old\n")
	;
		( It_num > Num ->
			widen(Old_eqns, New_eqns, Vars, Widened_eqns0),
			remove_redundant_eqns(Widened_eqns0, Widened_eqns)

		;
			Widened_eqns = New_eqns
		),

		% In the current implementation of widen, it suffices to test 
		% whether the number of equations in Old_eqns is equal to the 
		% number in Widened_equations if It_num > Num (that is, if 
		% widening took place).  
		% This test takes a lot longer, but is more robust under 
		% changes to the implementation of widen.
		
		test_fixpoint(New_eqns, Old_eqns, Vars, Changed_flag)
	).

:- pred test_fixpoint(equations, equations, size_varset, bool).
:- mode test_fixpoint(in, in, in, out) is det.
test_fixpoint(New_eqns, Old_eqns, Vars, Changed_flag) :-

	Entailed_by_new = lambda([Eqn::in] is semidet, (
		entailed(Eqn, New_eqns, Vars)
	)),
	list__filter(Entailed_by_new, Old_eqns, Unchanged_eqns),
	( list__same_length(Old_eqns, Unchanged_eqns) ->
		Changed_flag = no
	;
		Changed_flag = yes
	).


% no_stronger_parallel_constraints(Eqn, Old_eqns).  
% Check that there are no constraints in Old_eqns that are stronger
% than but parallel to Eqn.
:- pred no_stronger_parallel_constraints(equation, equations).
:- mode no_stronger_parallel_constraints(in, in) is semidet.

no_stronger_parallel_constraints(_, []).
no_stronger_parallel_constraints(Eqn, [Old_eqn|Old_eqns]) :-
	Eqn = eqn(Coeffs, (=<), Const),
	Old_eqn = eqn(Old_coeffs, (=<), Old_const),
	compare_var_lists(Coeffs, Old_coeffs, Var_result),
	compare_rat_lists(Coeffs, Old_coeffs, Rat_result),
	(
		Var_result = (=),
		Rat_result = (=),
		rat:'>='(Old_const, Const)  % parallel but old eqn not stronger.
	;
		Var_result \= (=)
	;
		Rat_result \= (=)
	),
	no_stronger_parallel_constraints(Eqn, Old_eqns).


% Initialises the bimap between size-vars and prog-vars.
:- pred fill_var_to_sizevar_map(hlds_goal, size_varset, size_varset, 
		bimap(prog_var, size_var)).
:- mode fill_var_to_sizevar_map(in, in, out, out) is det.

fill_var_to_sizevar_map(Goal, Varset0, Varset, VarToSizeVarMap) :-
	bimap__init(VarToSizeVarMap0),
	quantification__goal_vars(Goal, VarsSet),
	Insert_var = lambda([Var::in, Map0::in, Map::out, VSet0::in,
							VSet::out] is det, (
		varset__new_var(VSet0, SizeVar, VSet),
		bimap__set(Map0, Var, SizeVar, Map)
	)),
	set__to_sorted_list(VarsSet, Vars),
	list__foldl2(Insert_var, Vars, VarToSizeVarMap0, VarToSizeVarMap, 
						Varset0, Varset).



