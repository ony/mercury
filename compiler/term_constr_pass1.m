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

:- import_module bimap, list, hlds_module, hlds_pred, map, prog_data, 
				set, term_util.

% Need enough info to make traversal params.
:- pred find_arg_sizes_in_scc(list(pred_proc_id), module_info, size_varset, 
		pass_info, widening_info, module_info, size_varset, 
							io__state, io__state).  
:- mode find_arg_sizes_in_scc(in, in, in, in, in, out, out, di, uo) is det.

%XX Put this in term_util.
:- pred find_zero_size_vars(module_info, bimap(prog_var, size_var),
		map(prog_var, type), set(size_var)).
:- mode find_zero_size_vars(in, in, in, out) is det.

:- type widening_info
	--->	
		remove_parallel_constraints
	;
		widen_after_fixed_iterations(int).

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
			%### Should use info about max errors to collect?
	do_one_iteration(SCC, Module_info0, SizeVars0, Func_info, Widen_info, 
		It_num, Module_info1, SizeVars1, Change_flag, IO0, IO1),	

	( Change_flag = yes ->
		Next_it_num = It_num + 1,
		find_arg_sizes_in_scc2(SCC, Module_info1, SizeVars1, Pass_info,
			Widen_info, Next_it_num, Module_info, SizeVars, IO1, IO)
	;
		Module_info = Module_info1,
		IO = IO1,
		SizeVars = SizeVars1
	).


% Calculates the next approximation to the argument-size constraints
:- pred do_one_iteration(list(pred_proc_id), module_info, size_varset, 
	functor_info, widening_info, int, module_info, size_varset, bool, 
							io__state, io__state).
:- mode do_one_iteration(in, in, in, in, in, in, out, out, out, di, uo) 
									is det.

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
	%list__append(PPID_Constraints, SCC_Constraints, Constraints).
	

% Find the constraints for a single predicate, which may be part of a
% larger SCC.
% Should have a 'pass_info' structure with max_errors, functor info?
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
	%term_constr_traversal__init_traversal_params(Module_info0, Func_info, 
	%		PPID, Context, VarTypes, Traversal_params),

	lookup_proc_arg_size_info(Module_info0, PPID, Maybe_arg_size_info),

	(	Maybe_arg_size_info = no, 
		( It_num = 0 ->
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

			Change_flag = yes,
			%XX Check for eqns.
			%   Change_flag should simply be set after the
			%   following test.

			( Constraint_info = eqns(Constraints) ->
				update_arg_size_info(PPID, Constraints, Zeros, 
				VarToSizeVarMap, Module_info0, Module_info)
			;
				Module_info = Module_info0
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

		% Need to pass the old variable map to do_traversal 
		% because then the variables in the two sets of constraints 
		% will have the same correspondence to the variables in the
		% procedure.
		term_constr_traversal__init_traversal_params(Module_info0, 
			Func_info, PPID, Context, VarTypes, Zeros, 
					VarToSizeVarMap, Traversal_params),

		do_traversal(Goal, Traversal_params, SizeVars0, 
			constr_info(SizeVars,Unwidened_Constraint_info),IO0,IO),
		
		( 	Unwidened_Constraint_info = false_equation,

			%XX Should terminate more gracefully than this?
			error("term_constr_pass1: No equations after second
			iteration")
		;
			Unwidened_Constraint_info = eqns(Unwidened_Constraints),
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
	
	set_pred_proc_ids_arg_size_info([PPID], 
		constraints(Constraints, Zeros, VarMap), Mod_info0, 
								Mod_info). 


% This assumes that constraints already entered in module info (i.e. the
% old equations) are in canonical form and are sorted.
:- pred test_fixpoint_and_perhaps_widen(widening_info, size_varset, int, 
				equations, equations, equations, bool).
:- mode test_fixpoint_and_perhaps_widen(in, in, in, in, in, out, out) is det.

test_fixpoint_and_perhaps_widen(remove_parallel_constraints, _, _, 
		Unwidened_eqns0, Old_eqns, Widened_eqns, Changed_flag) :- 
	canonical_form(Unwidened_eqns0, Unsorted_eqns),
	list__sort(compare_eqns, Unsorted_eqns, Unwidened_eqns1), 	
	remove_redundant_eqns(Unwidened_eqns1, Unwidened_eqns),

	remove_weakening_constraints(Unwidened_eqns, Old_eqns, Widened_eqns,
								Changed_flag).

test_fixpoint_and_perhaps_widen(widen_after_fixed_iterations(Num), Vars, It_num,
		New_eqns, Old_eqns, Widened_eqns, Changed_flag) :-

	% This test should be unecessary if the algorithm is implemented
	% correctly.  Worth leaving in for now, though.
	Entailed_by_old = lambda([Eqn::in] is semidet, (
		entailed(Eqn, Old_eqns, Vars)
	)),
	list__filter(Entailed_by_old, New_eqns, Weaker_eqns),
	( \+ ( list__same_length(New_eqns, Weaker_eqns) ; It_num = 0) ->
		error("term_constr_pass1: New equations not entailed by old\n")
	;
		( It_num > Num ->
			widen(Old_eqns, New_eqns, Vars, Widened_eqns)
		;
			Widened_eqns = New_eqns
		),

		% In the current implementation of widen, it suffices to test 
		% whether the number of equations in Old_eqns is equal to the 
		% number in Widened_equations if It_num > Num (that is, if 
		% widening took place).  
		% This test takes a lot longer, but is more robust under 
		% changes to the implementation of widen.
		
		Entailed_by_new = lambda([Eqn::in] is semidet, (
			entailed(Eqn, New_eqns, Vars)
		)),
		list__filter(Entailed_by_new, Old_eqns, Unchanged_eqns),
		( list__same_length(Old_eqns, Unchanged_eqns) ->
			Changed_flag = no
		;
			Changed_flag = yes
		)
	).
	  

% If there are any constraints in the new constraints that are parallel to
% but weaker than a constraint in the old constraints, this removes them
% from the new constraints.  It also sets the Changed_flag to 'yes' if
% the new constraints are different from the old ones, 'no' otherwise.
:- pred remove_weakening_constraints(equations, equations, equations, bool).
:- mode remove_weakening_constraints(in, in, out, out) is det.

remove_weakening_constraints(New_eqns, Old_eqns, Widened_eqns, Cflag) :-
	remove_weakening_constraints2(New_eqns, Old_eqns, [], Wid_eqns, Cflag),
	list__reverse(Wid_eqns, Widened_eqns).

:- pred remove_weakening_constraints2(equations, equations, equations, 
							equations, bool).
:- mode remove_weakening_constraints2(in, in, in, out, out) is det.

remove_weakening_constraints2([], [], Widened_eqns, Widened_eqns, no).
remove_weakening_constraints2([Neqn|New_eqns], [], Acc, Widened_eqns, yes) :-
	remove_weakening_constraints2(New_eqns, [], [Neqn|Acc], Widened_eqns,_).
remove_weakening_constraints2([], [_|_], Widened_eqns, Widened_eqns, yes).
remove_weakening_constraints2([Neqn|New_eqns], [Oeqn|Old_eqns], Acc, 
						Widened_eqns, Change_flag) :-
	(
		Neqn = eqn(Ncoeffs, (=<), NConst),
		Oeqn = eqn(Ocoeffs, (=<), OConst)
	->
		compare_coeff_lists(Ncoeffs, Ocoeffs, Result),
		( 
			Result = (=),
			( rat:'='(NConst, OConst) ->
				remove_weakening_constraints2(New_eqns,Old_eqns,
					 [Neqn|Acc], Widened_eqns, Change_flag)
			;
				( rat:'>'(NConst, OConst) ->
					Change_flag = yes,
					remove_weakening_constraints2(New_eqns, 
						Old_eqns, Acc, Widened_eqns, _)	
				;
					error("term_constr_pass1: constraints \
					got tighter between iterations\n")
				)
			)
		;
			Result = (<),
			Change_flag = yes,
			remove_weakening_constraints2(New_eqns, [Oeqn|Old_eqns],
				[Neqn|Acc], Widened_eqns, _)
		;
			Result = (>),
			Change_flag = yes,
			remove_weakening_constraints2([Neqn|New_eqns], Old_eqns,
						 Acc, Widened_eqns, _)
		)
	;
		error("term_constr_pass1: Non_canonical equation in 
					remove_weakening_constraints\n")
	).
		

% Takes a list of equations sorted according to the compare_eqns function,
% and removes all equations for which a stronger parallel equation exists
% in the list (because the list is sorted, such an equation will occur
% next in the list).  This is necessary before widening by testing for
% parallel weaker equations, since otherwise we might widen unnecessarily.
% For example, if x =< 1 is in the old constraints and x =< 2 is in the new
% constraints, we don't need to remove this equation if x =< 1 also occurs
% in the new constraints.
:- pred remove_redundant_eqns(equations, equations).
:- mode remove_redundant_eqns(in, out) is det.

remove_redundant_eqns(Eqns1, Eqns2) :-
	remove_redundant_eqns2(Eqns1, [], Reversed_eqns2),
	list__reverse(Reversed_eqns2, Eqns2).


:- pred remove_redundant_eqns2(equations, equations, equations).
:- mode remove_redundant_eqns2(in, in, out) is det.

remove_redundant_eqns2([], Eqns, Eqns).
remove_redundant_eqns2([Eqn], Eqns, [Eqn|Eqns]).
remove_redundant_eqns2([Eqn1,Eqn2|Eqns], Acc_eqns, Output_eqns) :-
	Eqn1 = eqn(Coeffs1, Op1, Const1),
	Eqn2 = eqn(Coeffs2, Op2, Const2),
	( (Op1 = (=<), Op2 = (=<)) ->
		( Coeffs1 = Coeffs2 ->
			( rat:'<'(Const1, Const2) ->
				error("term_constr_pass1: Incorrectly sorted \
				list in remove_redundant_eqns\n")
			;
				remove_redundant_eqns2([Eqn2|Eqns], Acc_eqns, 
								Output_eqns)
			)
		;
			remove_redundant_eqns2([Eqn2|Eqns], [Eqn1|Acc_eqns], 
								Output_eqns)
		)
	;
		error("term_constr_pass1: Non-canonical equations in 
						remove_redundant_eqns\n")
	).


find_zero_size_vars(Module, VarToSizeVarMap, VarTypes, Zeros) :-
		% Find variables having zero-sized type
	Is_zero = lambda([VarA::in] is semidet, (
		lookup(VarTypes, VarA, Type),
		zero_size_type(Type, Module)
	)),
	bimap__ordinates(VarToSizeVarMap, Vars),
	list__filter(Is_zero, Vars, ZeroVars),

		% Build Zeros = corresponding size_vars
	VarToSize = lambda([VarB::in, SizeVar::out] is det, (
		lookup(VarToSizeVarMap, VarB, SizeVar)
	)),
	list__map(VarToSize, ZeroVars, ZerosList),
	list_to_set(ZerosList, Zeros).


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



