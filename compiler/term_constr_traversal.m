%-----------------------------------------------------------------------------%
% Copyright (C) 1995-1998 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% file: term_constr_traversal.m
% main author: vjteag 

% This module provides "do_traversal", that traverses a goal and
% collects constraints on arguments sizes for this goal.


:- module term_constr_traversal.

:- interface.

:- import_module bimap, hlds_goal, hlds_module, hlds_pred, io, 
	lp_rational, map, prog_data, set, term, term_util.  

:- pred do_traversal(hlds_goal, traversal_params, size_varset, 
				constraint_info, io__state, io__state).
:- mode do_traversal(in, in, in, out, di, uo) is det.


:- type traversal_params.


:- pred term_constr_traversal__init_traversal_params(module_info, functor_info,
	pred_proc_id, term__context, map(prog_var, type), set(size_var), 
	bimap(prog_var, size_var), traversal_params).
:- mode term_constr_traversal__init_traversal_params(in, in, in, in, in, in, 
								in, out) is det.

				
% derive_nonneg_eqns : takes a var-sizevar bimap and a size_var list, and 
% returns an "x >= 0" equation for every sizevar in the map that is not
% in the list. The list uses to be a zero-size variable list.
%### This should probably go in term_util?

:- pred derive_nonneg_eqns(bimap(prog_var, size_var), set(size_var), equations).
:- mode derive_nonneg_eqns(in, in, out) is det.

%------------------------------------------------------------------------------

:- implementation.

:- import_module assoc_list, bimap, hlds_data, hlds_goal, hlds_module, 
	hlds_pred, io, list, lp_rational, map, quantification, rat, require, 
	set, std_util, term, term_util, type_util, varset.

do_traversal(Goal, Params, Size_varset0, Constr_info, IO0, IO) :-

		% Build non negative eqns for non zero-sized sizevars
	params_get_zeros(Params, Zeros),
	params_get_var_to_sizevar_map(Params, VarToSizeVarMap),
	derive_nonneg_eqns(VarToSizeVarMap, Zeros, NonNegEqns),

	traverse_goal(Goal, Params, constr_info(Size_varset0, eqns(NonNegEqns)),
							Constr_info, IO0, IO).


:- pred traverse_goal(hlds_goal, traversal_params, constraint_info, 
		constraint_info, io__state, io__state).
:- mode traverse_goal(in, in, in, out, di, uo) is det.

traverse_goal(Goal, Params, Constr_info0, Constr_info, IO0, IO) :-
	Goal = GoalExpr-GoalInfo,
	(
		goal_info_get_determinism(GoalInfo, Detism),
		determinism_components(Detism, _, at_most_zero)
	->
			% Goals that return no solutions do not
			% need to be taken into account.
		Constr_info = Constr_info0,
		IO = IO0
	;
		traverse_goal_2(Goal, Params, Constr_info0, Constr_info1,
		 						IO0, IO),
		Constr_info1 = constr_info(Varset, Eqn_info),
		( goal_is_atomic(GoalExpr) ->  
			Constr_info = Constr_info1
		;
			( 	Eqn_info = false_equation,
				Constr_info = Constr_info1
			;
				Eqn_info = eqns(Constraints0),
				params_get_zeros(Params, Zeros),
				remove_zero_vars(Zeros, Constraints0, 
								Constraints1),
				get_local_vars(Goal, Locals),
				rename_vars_params(Locals,Locals_sizes, Params),
				project(Constraints1, Locals_sizes,Constraints),
				Constr_info = constr_info(Varset,
							eqns(Constraints))
			)
		)
			
	).


:- pred traverse_goal_2(hlds_goal, traversal_params, constraint_info,
					constraint_info, io__state, io__state).
:- mode traverse_goal_2(in, in, in, out, di, uo) is det.

traverse_goal_2(conj(Goals)-_, Params, Constr_info0, Constr_info1, 
								IO0, IO) :-
	
	traverse_conj(Goals, Params, Constr_info0, Constr_info1, IO0, IO).


traverse_goal_2(disj(Goals, _)-_, Params, Constr_info0, Constr_info, 
							IO0, IO) :-
	traverse_disj(Goals, Params, Constr_info0, Constr_info, IO0, IO).


traverse_goal_2(switch(_, _, Cases, _)-_, Params, Constr_info0, 
					Constr_info, IO0, IO) :-
	Get_goal = lambda([Case::in, Goal::out] is det, (
		Case = case(_, Goal)
	)),
	list__map(Get_goal, Cases, Goals),
	traverse_disj(Goals, Params, Constr_info0, Constr_info, IO0, IO).


traverse_goal_2(if_then_else(_, Cond, Then, Else, _)-_, Params, 
				Constr_info_in, Constr_info, IO0, IO) :-

	% The calls to traverse_conj and traverse_goal should have the same 
	% input constraints,
	% because they are disjoined, so the constraints appended to 
	% Constraints_in by traverse_conj should not be passed to 
	% traverse_goal.

	traverse_conj([Cond, Then], Params, Constr_info_in, Then_constr_info, 
							IO0, IO1),
	Then_constr_info = constr_info(Then_varset, Then_constraints),

	Constr_info_in = constr_info(_, Constraints_in),
	params_get_var_to_sizevar_map(Params, VarToSizeVarMap),
	params_get_zeros(Params, Zeros),
	derive_nonneg_eqns(VarToSizeVarMap, Zeros, NonNegs),
	combine_eqns(eqns(NonNegs), Constraints_in, Into_else_constraints),

	% XX In order to pass only Constraints_in for the ELSE goal and
	% to pass the not(Cond) in addition, should not this call be :
	% traverse_conj([not(Cond), Else], Params, constr_info(Then_varset,
	% Constraints_in), Else_constr_info, IO1, IO)
	% (and this way, you add the variables from Cond and the related
	% equations).
	traverse_goal(Else, Params, constr_info(Then_varset, 
		Into_else_constraints), constr_info(Else_varset, 
						Else_constraints), IO1, IO),


	( 	Then_constraints = false_equation,  
		Constr_info = constr_info(Else_varset, Else_constraints)
	;
		Then_constraints = eqns(Then_eqns),
		(	Else_constraints = false_equation, 
			Constr_info = constr_info(Else_varset, Then_constraints)
		;
			Else_constraints = eqns(Else_eqns),
			convex_hull([Then_eqns, Else_eqns],
					Conv_hull, Else_varset, Varset),

			Constr_info = constr_info(Varset, eqns(Conv_hull))
		)
	).



% Don't need to use the Vars explicitly given as existentially quantified
% in some(Vars, Goal), because this information is stored in goal_info
% which is checked by traverse_goal anyway.
traverse_goal_2(some(_Vars, Goal)-_, Params, Constr_info0, Constr_info, IO0, 
									IO) :-
	traverse_goal(Goal, Params, Constr_info0, Constr_info, IO0, IO).
	

traverse_goal_2(call(CallPredId, CallProcId, Args, _, _, _)-_, Params, 
		constr_info(Varset0, Constraints0), constr_info(Varset0,
			Constraints), IO0, IO) :-

  		% Get information about the relative sizes of the input
		% and output args of the procedure.
	params_get_module_info(Params, Module),
        module_info_pred_proc_info(Module, CallPredId, CallProcId, _,
                CallProcInfo),
	proc_info_get_maybe_arg_size_info(CallProcInfo, CallArgSizeInfo),

	(
		CallArgSizeInfo = no,
		Constraints = false_equation,
		IO = IO0
	;
		CallArgSizeInfo = yes(Size_info),
		( 
			Size_info = finite(_,_), 
			error("term_constr_traversal: Wrong type of Arg size \
			info")
		;
			Size_info = infinite(_),
			error("term_constr_traversal: Wrong type of Arg size \
			info")
		;	
			Size_info = constraints(Eqns, _Zeros, HeadToSizeVarMap)
		),

			% Build a size_var-size_var bimap (args to
			% headvars, i.e. New to Old) and then substitute 
			% in the original eqns to get new ones involving 
			% args sizevars.
		proc_info_headvars(CallProcInfo, Headvars),

		rename_vars_params(Args, RenamedArgs, Params),

		bimap__init(SizeToSizeVarMap0),
		compose_bijections(RenamedArgs, Headvars, 
			HeadToSizeVarMap, SizeToSizeVarMap0, SizeToSizeVarMap),
		
		substitute_size_vars(Eqns, SizeToSizeVarMap,EqnsInCorrectVbles),

			% Remove zero-sized vars from eqns.
		params_get_zeros(Params, CallingPredZeros),
		remove_zero_vars(CallingPredZeros, EqnsInCorrectVbles,  
				EqnsWithoutZeroSizeVars),
		
		io__write("term_constr_traversal:found equations :", IO0, IO1),
		io__nl(IO1, IO2),
		% XX These really aren't the variables we want to read about.
		write_equations(EqnsWithoutZeroSizeVars, IO2, IO3),	
		io__nl(IO3, IO),

		combine_eqns(eqns(EqnsWithoutZeroSizeVars), Constraints0, 
								Constraints)
	).



traverse_goal_2(unify(_, _RHS, _UniMode, Unification, _UniContext)-_,
		 Params, Constr_info0, Constr_info, IO0, IO) :-
	(
		Unification = construct(Var, ConsId, ArgVars0, Modes),
		( info_to_eqn(Var, ConsId, ArgVars0, Modes, Params, 
					Constr_info0, Constr_info_out) ->
			write_first_equation(Constr_info_out, IO0, IO),
			Constr_info = Constr_info_out
		;		
			Constr_info = Constr_info0,
			IO = IO0
		)
	;
		Unification = deconstruct(Var, ConsId, ArgVars0, Modes, _),
		( info_to_eqn(Var, ConsId, ArgVars0, Modes, Params, 
					Constr_info0, Constr_info_out) ->
			write_first_equation(Constr_info_out, IO0, IO),
			Constr_info = Constr_info_out
		;	
			Constr_info = Constr_info0,
			IO = IO0
		)
	;	
		Unification = assign(LVar, RVar),
		simple_info_to_eqn(LVar, RVar, Params,Constr_info0,Constr_info),
		write_first_equation(Constr_info, IO0, IO)
	;
		Unification = simple_test(LVar, RVar),
		simple_info_to_eqn(LVar, RVar, Params,Constr_info0,Constr_info),
		write_first_equation(Constr_info, IO0, IO)
	;
		Unification = complicated_unify(_,_),
         	error("Unexpected complicated_unify in termination analysis")
	).
      
traverse_goal_2(not(Goal)-_, Params, constr_info(Varset0, Constrs),
			constr_info(Varset, Constrs), IO0, IO) :-

	traverse_goal(Goal, Params, constr_info(Varset0, Constrs),
			constr_info(Varset, _), IO0, IO).

traverse_goal_2(pragma_c_code(_, _, _, _, _, _, _)-_, _, Constr_info,
							Constr_info, IO, IO).

traverse_goal_2(higher_order_call(_, _, _, _, _, _)-_, _, Constr_info,
							Constr_info, IO, IO).

traverse_goal_2(class_method_call(_, _, _, _, _, _)-_, _, Constr_info,
							Constr_info, IO, IO).

traverse_goal_2(par_conj(Goals, _)-_, Params, Constr_info0, 
						Constr_info, IO0, IO) :-
	traverse_conj(Goals, Params, Constr_info0, Constr_info, IO0, IO).

	%get_local_vars(par_conj(Goals, SMap)-Goal_info, Locals),
	%params_get_ppid(Params, PPID),
	%rename_vars_params(Locals, Renamed_locals, Params, Constr_info1, 
	%							Constr_info2),

	%Constr_info2 = constr_info(Map, Vars, Zeros, Constraints2),
	%project(Constraints2, Renamed_locals, Constraints),
	%Constr_info = constr_info(Map, Vars, Zeros, Constraints).


%------------------------------------------------------------------------------

:- pred traverse_conj(hlds_goals, traversal_params, constraint_info,
				constraint_info, io__state, io__state).
:- mode traverse_conj(in, in, in, out, di, uo) is det.

traverse_conj([], _, Constr_info, Constr_info, IO, IO).  

traverse_conj([Goal|Goals], Params, Constr_info0, Constr_info, IO0, IO) :-
	traverse_goal(Goal, Params, Constr_info0, Constr_info1, IO0, IO1),
	traverse_conj(Goals, Params, Constr_info1, Constr_info, IO1, IO).


% For a disjunction of constraints C1 \/ C2 \/ ... \/ Cn, and an initial
% set of constraints C, this computes the convex hull of
% (C /\ C1, C /\ C2, ..., C /\ Cn).  This is slower than computing
% C /\ conv_hull( C1, C2, C3, ..., Cn), but it gives a tighter bound.
:- pred traverse_disj(hlds_goals, traversal_params, constraint_info, 
				constraint_info, io__state, io__state).
:- mode traverse_disj(in, in, in, out, di, uo) is det.

traverse_disj(Goals, Params, Constr_info0, Constr_info, IO0, IO):-

	traverse_disj_acc(Goals, Params, [], Disj_constraints, 
					Constr_info0, Varset1, IO0, IO),
					% the constraints passed out as    
					% constraint_info should be exactly the
					% initial ones.                    

	Make_polys = lambda([Eqn_info::in, Constrs0::in, Constrs::out] is det, (
		( 	Eqn_info = false_equation,
			Constrs = Constrs0
		;
			Eqn_info = eqns(Eqns),
			Constrs = [Eqns | Constrs0 ]
		)
	)),
	list__foldl(Make_polys, Disj_constraints, [], Non_false_polys),

	( Non_false_polys = [] ->
		( Disj_constraints = [] ->
			%XXX Can this ever happen? (i.e. can we traverse
			% a disjunction and find no info in a disjunct
			% though we don't find a false equation?).
			Constr_info = constr_info(Varset1, eqns([]))
		;
			Constr_info = constr_info(Varset1, false_equation)
		)
	;
		convex_hull(Non_false_polys, Poly, Varset1, Varset),
		Constr_info = constr_info(Varset, eqns(Poly))
	).

% Each pass of this traverses one disjunct, updates the size-varset and
% sizevar-var map, and adds any constraints that are found to the list
% of disjunctive constraints.  It is called recursively with the
% old set of constraints (since we don't want to 'and' together two
% branches of a disjunct) and the updated variable information (since
% the same variables are likely to be encountered in more than one
% disjunct).
:- pred traverse_disj_acc(hlds_goals, traversal_params, 
	list(eqn_info), list(eqn_info), constraint_info, size_varset, 
							io__state, io__state).
:- mode traverse_disj_acc(in, in, in, out, in, out, di, uo) is det.

traverse_disj_acc([], _, Disj_constraints, Disj_constraints,
					constr_info(Varset, _), Varset, IO, IO).

traverse_disj_acc([Goal|Goals], Params, Disjunction_constraints0, 
		Disjunction_constraints, Constr_info_top, Varset, IO0, IO) :-

	Constr_info_top = constr_info(_, Constraints_top),
	
	traverse_goal(Goal, Params, Constr_info_top,
		Constr_info_disjunct, IO0, IO1),
	
	Constr_info_disjunct = constr_info(Varset_disjunct, 
							Constraints_disjunct),

	Disjunction_constraints1 = [Constraints_disjunct | 
					Disjunction_constraints0],

	Constr_info = constr_info(Varset_disjunct, Constraints_top),

	traverse_disj_acc(Goals, Params, Disjunction_constraints1, 
		Disjunction_constraints, Constr_info, Varset, IO1, IO).


%-----------------------------------------------------------------------------

derive_nonneg_eqns(Bimap, Zeros, NonNegs) :-
	bimap__coordinates(Bimap, Sizevars),

	Not_zero_size = lambda([SizeA::in] is semidet, (
		\+ set__member(SizeA, Zeros)
	)),
	list__filter(Not_zero_size, Sizevars, NonZeroSizevars),

	Make_nonneg_eqn = lambda([SizeB::in, Eqn::out] is det, (
		Eqn = eqn([SizeB-one],(>=), zero)
	)),
	list__map(Make_nonneg_eqn, NonZeroSizevars, NonNegs).


% Forms the conjunction of the first two sets of equations.
% If one of these is false_equation, the result is false_equation.
% Otherwise, it appends the two lists.
:- pred combine_eqns(eqn_info, eqn_info, eqn_info).
:- mode combine_eqns(in, in, out) is det.

combine_eqns(false_equation, false_equation, false_equation).
combine_eqns(false_equation, eqns(_), false_equation).
combine_eqns(eqns(_), false_equation, false_equation).
combine_eqns(eqns(Eqns0), eqns(Eqns1), eqns(Eqns)) :-
	append(Eqns0, Eqns1, Eqns).


:- pred write_first_equation(constraint_info, io__state, io__state).
:- mode write_first_equation(in, di, uo) is det.

write_first_equation(Constr_info, IO0, IO) :-
	( Constr_info = constr_info(_, eqns([Eqn|_])) ->
		io__write("found equation ", IO0, IO1),
		write_equations([Eqn], IO1, IO)
	;
		IO = IO0
	).

%-----------------------------------------------------------------------------

% info_to_eqn : Takes some info about a unification and appends to the
% current constraints the
% equation that corresponds to it.  Used for deconstruction and 
% construction unifications.  i.e. for a unification of the form
% X = f(U,V,W), if the functor norm counts the first and
% second arguments, the equation returned is |X| - |U| - |V| = |f|.
% This predicate fails when called for higher-order unifications,
% or unifications which produce an equation 0=0.
% 

:- pred info_to_eqn(prog_var, cons_id, list(prog_var), list(uni_mode),
		traversal_params, constraint_info, constraint_info).
:- mode info_to_eqn(in, in, in, in, in, in, out) is semidet.

info_to_eqn(Var, ConsId, ArgVars0, Modes, Params, Constr_info0, Constr_info) :-

	params_get_functor_info(Params, FunctorInfo),
	params_get_var_types(Params, VarTypes),	
	map__lookup(VarTypes, Var, Type),
	
	params_get_module_info(Params, Module),

		% Fails for higher-order unifications.
	\+ type_is_higher_order(Type, _, _),
	
		% Build the equation, except if Var has a variable type 
		% (i.e. polymorphic, ...).
	( type_to_type_id(Type, TypeId, _) ->
		functor_norm(FunctorInfo, TypeId, ConsId, Module, 
			Const, ArgVars0, CountedVars, Modes, _) 

		% So eqn is Var = Const + sum(CountedVars).
	
	;
		error("variable type in info_to_eqn")	
	),
	
	params_get_zeros(Params, Zeros),
	params_get_var_to_sizevar_map(Params, VarToSizeVarMap),
		
	rename_var(Var, NewVar, VarToSizeVarMap),

	%XXX Maybe just leave zero vars in and leave them to be removed
	% by remove_zero_vars in traverse_goal.
	( set__member(NewVar, Zeros) ->
		First_coeff = []
	;
		First_coeff = [NewVar-rat(1,1)]
	),

	Add_coeff = lambda([Var1::in, Coeffs0::in, Coeffs1::out] is det, (
		rename_var(Var1, NVar1, VarToSizeVarMap),
		( set__member(NVar1, Zeros) ->
			Coeffs1 = Coeffs0
		;
			Coeffs1 = [NVar1-rat(-1,1) | Coeffs0]
		)
	)),

	list__foldl(Add_coeff, CountedVars, First_coeff, Coeffs),

	( 	Coeffs = [], 
		Const \= 0  
	-> 
		error("term_constr_traversal: error in calculating equation")
	;
		Coeffs \= [],
		Constr_info0 = constr_info(Varset0, Constraints0),
		combine_eqns(eqns([eqn(Coeffs,(=),rat(Const,1))]), Constraints0,
							NewConstraints),
		Constr_info = constr_info(Varset0, NewConstraints)
	).	

% simple_info_to_eqn : Takes some info about a unification and appends to the
% current constraints the
% equation that corresponds to it.  Used for assignment and simple_test
% unifications.  i.e. for a unification of the form X = Y,
% the equation returned is |X| - |Y| = 0.
:- pred simple_info_to_eqn(prog_var, prog_var, traversal_params,
		constraint_info, constraint_info).
:- mode simple_info_to_eqn(in, in, in, in, out) is det.

simple_info_to_eqn(LVar, RVar, Params, Constr_info0, Constr_info) :-

	params_get_zeros(Params, Zeros),
	params_get_var_to_sizevar_map(Params, VarToSizeVarMap),

	rename_var(LVar, NewLVar, VarToSizeVarMap),
	rename_var(RVar, NewRVar, VarToSizeVarMap),

	( (set__member(NewLVar, Zeros), set__member(NewRVar, Zeros)) ->

		% Don't bother adding "0 = 0"
		Constr_info = Constr_info0
	;
		(  (set__member(NewLVar, Zeros) ; set__member(NewRVar, Zeros))->
			error("Unification of a zero-size var and another \
			type of var")
		;
			Constr_info0 = constr_info(Varset0, Constraints0),

			Eqn = eqn([NewLVar-rat(1,1), NewRVar-rat(-1,1)], (=), 
									zero),
			combine_eqns(eqns([Eqn]), Constraints0, NewConstrs),
			Constr_info = constr_info(Varset0, NewConstrs)
		)
	).



% Because quantification returns a conservative estimate of nonlocal
% vars, this returns a list of local vars which may omit some of 
% the real local vars.  #### This may be a problem!
%                       According to Tom, this should work. (They use
%                       pretty the same in the code generator.)
:- pred get_local_vars(hlds_goal, list(prog_var)).
:- mode get_local_vars(in, out) is det.

get_local_vars(Goal_expr-Goal_info, Locals) :-
	goal_info_get_nonlocals(Goal_info, Nonlocals),
	quantification__goal_vars(Goal_expr-Goal_info, Quant_vars),
	set__difference(Quant_vars, Nonlocals, Locals_set),
	set__to_sorted_list(Locals_set, Locals).


% substitute_size_vars: Takes a list of equations and a set of substitutions
% (as a map from size_var to size_var).  Returns the equations with the required
% substitutions. 
:- pred substitute_size_vars(equations, bimap(size_var, size_var), equations).
:- mode substitute_size_vars(in, in, out) is det.

substitute_size_vars(Eqns, NewToOldVarMap, EqnsInCorrectVbles) :-

	SubVarInCoeff = lambda([OldVar-Rat::in, NewVar-Rat::out] is det, (
		bimap__reverse_lookup(NewToOldVarMap, NewVar, OldVar) 
	)),
	
	SubVarInEqn = lambda([eqn(Coeffs0, Op, Rat)::in, 
					eqn(Coeffs, Op, Rat)::out] is det, (
		list__map(SubVarInCoeff, Coeffs0, Coeffs)
	)),
	
	list__map(SubVarInEqn, Eqns, EqnsInCorrectVbles).


% compose_bijections: takes two lists of vars of equal length, each list with 
% a corresponding map from the vars in the list to size_vars.  There is an 
% implicit bijection between the two lists (based on the order of the lists).
% This predicate composes all three maps to produce a map from sizevar to 
% sizevar (keys are the elements of the first list, values the values in
% the first map).

:- pred compose_bijections(list(size_var), list(prog_var),
		bimap(prog_var, size_var), bimap(size_var, size_var),
		bimap(size_var, size_var)).
:- mode compose_bijections(in, in, in, in, out) is det.

compose_bijections([], [], _, SizeVars, SizeVars).
compose_bijections([_|_], [], _, _, _) :-
	error("traverse_goal_2: incorrect number of vars in call\n").
compose_bijections([], [_|_], _, _, _) :-
	error("traverse_goal_2: incorrect number of vars in call\n").

compose_bijections([ArgSize|Args], [HeadVar|Headvars], HeadToSizeVarMap, 
			SizeVarMap0, SizeVarMap):-

	(bimap__search(HeadToSizeVarMap, HeadVar, HeadVarSize) -> 

		(bimap__insert(SizeVarMap0, ArgSize, HeadVarSize, SizeVarMap1)->
			compose_bijections(Args, Headvars, HeadToSizeVarMap, 
							SizeVarMap1, SizeVarMap)
		;
			error("term_constr_traversal: size vars not unique")
		)
	;
		% We expect that type-info variables won't be in the map.
		% XXXX Check that this is still valid - do type_info varables
		% occur in the map in proc_info?

		% That's fine, as long as they don't turn up in the equations,
		% (which they shouldn't, for exactly the same reason that they
		% aren't in the map).

		%XXX Check here that the missing variable is a type-info
		% variable?
		compose_bijections(Args, Headvars, HeadToSizeVarMap,
						SizeVarMap0, SizeVarMap)
	).
%-----------------------------------------------------------------------------

:- pred rename_vars_params(list(prog_var), list(size_var), traversal_params). 
:- mode rename_vars_params(in, out, in) is det.

rename_vars_params(Vars, SizeVars, Params) :-
	params_get_var_to_sizevar_map(Params, VarToSizeVarMap),
	rename_vars(Vars, SizeVars, VarToSizeVarMap).

%-----------------------------------------------------------------------------

% XX Obsolete
:- pred has_false_eqn(equations).
:- mode has_false_eqn(in) is semidet.

has_false_eqn([Eqn|_]) :-
	is_false(Eqn).
has_false_eqn([_|Eqns]) :-
	has_false_eqn(Eqns).

%-----------------------------------------------------------------------------


:- type traversal_params
	--->	traversal_params(
   			module_info,
                        functor_info,
                        pred_proc_id,   	% The procedure we are tracing 
						% through.
                        term__context,  	% The context of the procedure.
			map(prog_var, type),
			set(size_var),		% Variables with zero-size type.
			bimap(prog_var, size_var) % Map from proc variables to
						% size_vars used in
						% constraints.
		). 


term_constr_traversal__init_traversal_params(ModuleInfo, FunctorInfo, 
	PredProcId, Context, VarTypeMap, Zeros, VarToSizeVarMap, Params) :-
        Params = traversal_params(ModuleInfo, FunctorInfo, PredProcId, Context,
		VarTypeMap, Zeros, VarToSizeVarMap).  

:- pred params_get_module_info(traversal_params::in, module_info::out)
        is det.
:- pred params_get_functor_info(traversal_params::in, functor_info::out)
        is det.
:- pred params_get_ppid(traversal_params::in, pred_proc_id::out)
        is det.
:- pred params_get_context(traversal_params::in, term__context::out)
        is det.
:- pred params_get_var_types(traversal_params::in, map(prog_var, type)::out)
        is det.
:- pred params_get_zeros(traversal_params::in, set(size_var)::out)
        is det.
:- pred params_get_var_to_sizevar_map(traversal_params::in, 
			bimap(prog_var, size_var)::out) is det.

params_get_module_info(Params, A) :-
        Params = traversal_params(A, _, _, _, _, _, _).

params_get_functor_info(Params, B) :-
        Params = traversal_params(_, B, _, _, _, _, _).

params_get_ppid(Params, C) :-
        Params = traversal_params(_, _, C, _, _, _, _).

params_get_context(Params, D) :-
        Params = traversal_params(_, _, _, D, _, _, _).

params_get_var_types(Params, E) :-
        Params = traversal_params(_, _, _, _, E, _, _).

params_get_zeros(Params, F) :-
        Params = traversal_params(_, _, _, _, _, F, _).

params_get_var_to_sizevar_map(Params, G) :-
        Params = traversal_params(_, _, _, _, _, _, G).
