%-----------------------------------------------------------------------------%
% Copyright (C) 1995-1998 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% file: term_constr_traversal.m
% main author: vjteag 


:- module term_traversal2.

:- interface.

:- import_module bimap, hlds_goal, hlds_module, hlds_pred, io, 
		lp_rational, map, prog_data, size_varset, term, term_util.  

%#### This should output module info.  No, it shouldn't.  It never changes it.
:- pred do_traversal(hlds_goal, traversal_params, constraint_info, 
				constraint_info, io__state, io__state).
:- mode do_traversal(in, in, in, out, di, uo) is det.


:- type traversal_params.


:- pred term_traversal2__init_traversal_params(module_info, functor_info,
	pred_proc_id, term__context, map(var, type), traversal_params).
:- mode term_traversal2__init_traversal_params(in, in, in, in, in, out) is det.

				
% derive_nonneg_eqns : takes a var-sizevar bimap and returns an
% "x >= 0" equation for every sizevar in the map.
%### This should probably go in term_util?

:- pred derive_nonneg_eqns(bimap(var,size_var), equations).
:- mode derive_nonneg_eqns(in, out) is det.

%------------------------------------------------------------------------------

:- implementation.

:- import_module assoc_list, bimap, hlds_data, hlds_goal, hlds_module, 
	hlds_pred, io, list, lp_rational, map, quantification, rat, require, 
	set, std_util, term, term_util, type_util, size_varset, varset.

do_traversal(Goal, Params, Constr_info0, Constr_info, IO0, IO) :-
	
	traverse_goal(Goal, Params, Constr_info0, Constr_info, IO0, IO).

	%params_get_ppid(Params, PPID),
	%unrename_eqns(PPID, Constraints0, BiMap, Constraints).
	% updating arg size info will be done one level up.  So will 
	% updating the vars-sizevars map in proc info.


% constraints carried in 'Constraints' (in constraint_info) argument(s) 
% always contain only
% renamed variables - it won't work if some are renamed and others aren't
% because (a) there may be clashes, and (b) project won't work properly
% because it won't notice that a given var is the same as its renamed
% version.
:- pred traverse_goal(hlds_goal, traversal_params, constraint_info, 
		constraint_info, io__state, io__state).
:- mode traverse_goal(in, in, in, out, di, uo) is det.

traverse_goal(Goal, Params, Constr_info0, Constr_info, IO0, IO) :-
	Goal = _GoalExpr-GoalInfo,
	(
		goal_info_get_determinism(GoalInfo, Detism),
		determinism_components(Detism, _, at_most_zero)
	->
		Constr_info = Constr_info0,
		IO = IO0
	;
		traverse_goal_2(Goal, Params, Constr_info0, Constr_info,IO0, IO)
	).


:- pred traverse_goal_2(hlds_goal, traversal_params, constraint_info,
					constraint_info, io__state, io__state).
:- mode traverse_goal_2(in, in, in, out, di, uo) is det.

traverse_goal_2(conj(Goals)-Goal_info, Params, Constr_info0,
		constr_info(VarMap, Varset, Zeros, Constraints), IO0, IO) :-
	
	traverse_conj(Goals, Params, Constr_info0, Constr_info1, IO0, IO),

	get_local_vars(conj(Goals)-Goal_info, Locals),
	rename_vars_params(Locals, Locals_sizes, Params, Constr_info1, 
			constr_info(VarMap, Varset, Zeros, Constraints2)),

	project(Constraints2, Locals_sizes, Constraints).


traverse_goal_2(disj(Goals, SM)-Goal_info, Params, Constr_info0, Constr_info, 
							IO0, IO) :-
	traverse_disj(Goals, Params, Constr_info0, Constr_info1, IO0, IO),

	get_local_vars(disj(Goals, SM)-Goal_info, Locals),
	rename_vars_params(Locals, Locals_sizes, Params, Constr_info1, 
								Constr_info2),

	Constr_info2 = constr_info(Map, Vars, Zeros, Constrs2),
	project(Constrs2, Locals_sizes, Constrs),
	Constr_info = constr_info(Map, Vars, Zeros, Constrs).

traverse_goal_2(switch(V, CF, Cases, SM)-Goal_info, Params, Constr_info0, 
					Constr_info, IO0, IO) :-
	Get_goal = lambda([Case::in, Goal::out] is det, (
		Case = case(_, Goal)
	)),
	list__map(Get_goal, Cases, Goals),
	traverse_disj(Goals, Params, Constr_info0, Constr_info1, IO0, IO),

	get_local_vars(switch(V, CF, Cases, SM)-Goal_info, Locals),
	rename_vars_params(Locals, Locals_sizes, Params, Constr_info1, 
								Constr_info2),

	Constr_info2 = constr_info(Map, Vars, Zeros, Constrs2),
	project(Constrs2, Locals_sizes, Constrs),
	Constr_info = constr_info(Map, Vars, Zeros, Constrs).



traverse_goal_2(if_then_else(LVs, Cond, Then, Else, SM)-Goal_info, Params, 
				Constr_info_in, Constr_info, IO0, IO) :-

	% The calls to traverse_conj and traverse_goal should have the same 
	% input constraints,
	% because they are disjoined, so the constraints appended to 
	% Constraints0 by traverse_conj should not be passed to 
	% traverse_goal, except the non-negativity constraints.  
	% The output var_info from traverse_conj should be
	% passed to traverse_goal, to avoid name clashes and also because
	% vars may appear in both the 'Then' and the 'Else' part.

	traverse_conj([Cond, Then], Params, Constr_info_in, Then_constr_info, 
							IO0, IO1),

	Constr_info_in = constr_info(_, _, _, Constraints_in),
	Then_constr_info = constr_info(Then_map, Then_varset, Then_zeros, 
							Then_constraints),

	derive_nonneg_eqns(Then_map, NonNegs),
	append(NonNegs, Constraints_in, Into_else_constraints),

	traverse_goal(Else, Params, constr_info(Then_map, Then_varset,
		Then_zeros, Into_else_constraints), constr_info(Else_map, 
			Else_varset, Else_zeros, Else_constraints), IO1, IO),


	get_local_vars(if_then_else(LVs, Cond, Then, Else,SM)
				-Goal_info, Locals),

	( has_false_eqn(Then_constraints) -> 
		( has_false_eqn(Else_constraints) ->

			false_eqn(False_eqn),
			Constr_info = constr_info(Else_map, Else_varset,
				Else_zeros, [False_eqn])
		;

			rename_vars_params(Locals, Locals_sizes, Params,
				constr_info(Else_map, Else_varset, Else_zeros,
						Else_constraints),
				constr_info(Map_out, Varset_out, Zeros_out,
						Unprojected_constraints)),

			project(Unprojected_constraints, Locals_sizes, 
							Constraints_out),
	
			Constr_info = constr_info(Map_out, Varset_out, 
						Zeros_out, Constraints_out)
		)
	;
		( has_false_eqn(Else_constraints) ->

			rename_vars_params(Locals, Locals_sizes, Params,
				constr_info(Else_map, Else_varset, Else_zeros,
						Then_constraints),
				constr_info(Map_out, Varset_out, Zeros_out,
						Unprojected_constraints))
		;

			convex_hull([Then_constraints, Else_constraints],
					Conv_hull, Else_varset, Varset3),

			rename_vars_params(Locals, Locals_sizes, Params, 
				constr_info(Else_map, Varset3, Else_zeros, 
								Conv_hull), 
				constr_info(Map_out, Varset_out, Zeros_out, 
						Unprojected_constraints))
		),
		project(Unprojected_constraints, Locals_sizes, 
						Constraints_out),

		Constr_info = constr_info(Map_out, Varset_out, 
					Zeros_out, Constraints_out)
	).



% Don't need to use the Vars explicitly given as existentially quantified
% in some(Vars, Goal), because this information is stored in goal_info
% which is checked by traverse_goal anyway.
traverse_goal_2(some(_Vars, Goal)-_, Params, Constr_info0, Constr_info, IO0, 
									IO) :-
	traverse_goal(Goal, Params, Constr_info0, Constr_info, IO0, IO).
	

traverse_goal_2(call(CallPredId, CallProcId, Args, _, _, _)-_, Params, 
				Constr_info0, Constr_info, IO0, IO) :-

  	params_get_module_info(Params, Module),
        %params_get_ppid(Params, PPId),
        %CallPPId = proc(CallPredId, CallProcId),

        module_info_pred_proc_info(Module, CallPredId, CallProcId, _,
                CallProcInfo),

	% Will need to write a new version of this predicate for the
	% new representation of arg contraints.
	proc_info_get_maybe_arg_size_info(CallProcInfo, CallArgSizeInfo),

	% Need termination info in second pass.
	%proc_info_get_maybe_termination_info(CallProcInfo,CallTerminationInfo),


	% We should rename the Args and insert them into the map even if we 
	% don't know equations for this call, because if any of the args
	% are non-local, their non-negativity equations will be needed 
	% later.
	rename_vars_params(Args, RenamedArgs, Params,Constr_info0,Constr_info1),
	(
		CallArgSizeInfo = no,
		Constr_info = Constr_info1,
		XXXXX
		IO = IO0
	;
		CallArgSizeInfo = yes(Size_info),
		( 
			Size_info = finite(_,_), 
			error("term_traversal2: Wrong type of Arg size info")
		;
			Size_info = infinite(_),
			error("term_traversal2: Wrong type of Arg size info")
		;	
			Size_info = constraints(Eqns, _Zeros, HeadToSizeVarMap)
		),

		proc_info_headvars(CallProcInfo, Headvars),


		% Need to filter out headvars that have zero-size type,
		% so that the headvars and args lists correspond.

		proc_info_vartypes(CallProcInfo, HeadVarTypeMap),
		Not_zero_size = lambda([Var::in] is semidet, (
			map__lookup(HeadVarTypeMap, Var, Type),
			\+ zero_size_type(Type, Module)
		)),

		list__filter(Not_zero_size, Headvars, NonZeroHeadvars), 


		bimap__init(SizeToSizeVarMap0),
		compose_bijections(RenamedArgs, NonZeroHeadvars, 
			HeadToSizeVarMap, SizeToSizeVarMap0, SizeToSizeVarMap),
		
		substitute_size_vars(Eqns, SizeToSizeVarMap,EqnsInCorrectVbles),
		io__write("term_traversal2:found equations :", IO0, IO1),
		io__nl(IO1, IO2),
		% These really aren't the variables we want to read about.
		write_equations(EqnsInCorrectVbles, IO2, IO3),	
		io__nl(IO3, IO),

		Constr_info1 = constr_info(Map, Varset, Zeros, Constraints1),
		append(EqnsInCorrectVbles, Constraints1, Constraints),
		Constr_info = constr_info(Map, Varset, Zeros, Constraints)
	).



traverse_goal_2(unify(_, _RHS, _UniMode, Unification, _UniContext)-_,
		 Params, Constr_info0, Constr_info, IO0, IO) :-
	%params_get_ppid(Params, PPID),
	(
		Unification = construct(Var, ConsId, ArgVars0, Modes),
		XX Put in a predicate.
		( info_to_eqn(Var, ConsId, ArgVars0, Modes, Params, 
					Constr_info0, Constr_info_out) ->
			( Constr_info_out = constr_info(_, _, _, [Eqn|_]) ->
				io__write("found equation ", IO0, IO1),
				io__nl(IO1, IO2),
				write_equations([Eqn], IO2, IO3),
				io__nl(IO3, IO)
			;
				IO = IO0
			),
			Constr_info = Constr_info_out
		;			% All but the constr_info lines are
					% only useful for debugging.
			Constr_info = Constr_info0,
			IO = IO0
		)
	;
		Unification = deconstruct(Var, ConsId, ArgVars0, Modes, _),
		( info_to_eqn(Var, ConsId, ArgVars0, Modes, Params, 
					Constr_info0, Constr_info_out) ->
			( Constr_info_out = constr_info(_, _, _, [Eqn|_]) ->
				io__write("found equation ", IO0, IO1),
				write_equations([Eqn], IO1, IO)
			;
				IO = IO0
			),
			Constr_info = Constr_info_out
		;			% All but the constr_info lines are
					% only useful for debugging.
			Constr_info = Constr_info0,
			IO = IO0
		)
	;	
		Unification = assign(LVar, RVar),
		simple_info_to_eqn(LVar, RVar, Params,Constr_info0,Constr_info),
		( Constr_info = constr_info(_, _, _, [Eqn|_]) ->
			io__write("found equation ", IO0, IO1),
			write_equations([Eqn], IO1, IO)
		;
			IO = IO0
		)
	;
		Unification = simple_test(LVar, RVar),
		simple_info_to_eqn(LVar, RVar, Params,Constr_info0,Constr_info),
		( Constr_info = constr_info(_, _, _, [Eqn|_]) ->
			io__write("found equation ", IO0, IO1),
			write_equations([Eqn], IO1, IO)
		;
			IO = IO0
		)
	;
		Unification = complicated_unify(_,_),
         	error("Unexpected complicated_unify in termination analysis")
	).
      
traverse_goal_2(not(Goal)-_, Params, constr_info(Map0, Varset0, Zeros0,Constrs),
			constr_info(Map, Varset, Zeros, Constrs), IO0, IO) :-

	traverse_goal(Goal, Params, constr_info(Map0, Varset0, Zeros0, Constrs),
			constr_info(Map, Varset, Zeros, _), IO0, IO).

traverse_goal_2(pragma_c_code(_, _, _, _, _, _, _)-_, _, Constr_info,
							Constr_info, IO, IO).

traverse_goal_2(higher_order_call(_, _, _, _, _, _)-_, _, Constr_info,
							Constr_info, IO, IO).

traverse_goal_2(class_method_call(_, _, _, _, _, _)-_, _, Constr_info,
							Constr_info, IO, IO).

traverse_goal_2(par_conj(Goals, SMap)-Goal_info, Params, Constr_info0, 
						Constr_info, IO0, IO) :-
	traverse_conj(Goals, Params, Constr_info0, Constr_info1, IO0, IO),

	get_local_vars(par_conj(Goals, SMap)-Goal_info, Locals),
	%params_get_ppid(Params, PPID),
	rename_vars_params(Locals, Renamed_locals, Params, Constr_info1, 
								Constr_info2),

	Constr_info2 = constr_info(Map, Vars, Zeros, Constraints2),
	project(Constraints2, Renamed_locals, Constraints),
	Constr_info = constr_info(Map, Vars, Zeros, Constraints).


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
					Constr_info0, Constr_info1, IO0, IO),
					% the constraints passed out as    
					% constraint_info should be exactly the
					% initial ones.                    

	Has_no_false_eqns = lambda([Eqns::in] is semidet, (
		\+ has_false_eqn(Eqns)
	)),
	list__filter(Has_no_false_eqns, Disj_constraints, Non_false_eqns),

	Constr_info1 = constr_info(Bmap, Vars1, Zeros, _),
	(Non_false_eqns \= [] ->
		convex_hull(Disj_constraints, Constraints, Vars1, Vars),
		Constr_info = constr_info(Bmap, Vars, Zeros, Constraints)
	;
		false_eqn(False_eqn),
		Constr_info = constr_info(Bmap, Vars1, Zeros, [False_eqn])
	).

% Is it necessary to project out the variables only contained in the
% disjunction, or will these have only occured in the goals in the list
% and therefore have already been removed?
% Ans: They will be projected out when this returns to traverse_goal_2.

% Each pass of this traverses one disjunct, updates the size-varset and
% sizevar-var map, and adds any constraints that are found to the list
% of disjunctive constraints.  It is called recursively with the
% old set of constraints (since we don't want to 'and' together two
% branches of a disjunct) and the updated variable information (since
% the same variables are likely to be encountered in more than one
% disjunct).
:- pred traverse_disj_acc(hlds_goals, traversal_params, 
	list(equations), list(equations), constraint_info, constraint_info, 
						io__state, io__state).
:- mode traverse_disj_acc(in, in, in, out, in, out, di, uo) is det.

traverse_disj_acc([], _, Disj_constraints, Disj_constraints, Constr_info, 
							Constr_info, IO, IO).

traverse_disj_acc([Goal|Goals], Params, Disj_constraints0, 
	Disj_constraints, Constr_info_top, Constr_info_final, IO0, IO) :-

	Constr_info_top = constr_info(_, _, _, Constraints_top),

	traverse_goal(Goal, Params, Constr_info_top,
		Constr_info_prev_disjunct, IO0, IO1),

	Constr_info_prev_disjunct = constr_info(Map_prev, Varset_prev, 
					Zeros_prev, Constraints_prev),
	Disj_constraints1 = [Constraints_prev | Disj_constraints0],

	% The next call to traverse_disj_acc gets: The Map, Varset, Zeros
	% and non-negativity equations from the previous disjunct and 
	% equations from before the beginning of the disjunction.

	derive_nonneg_eqns(Map_prev, NonNegs),
	append(NonNegs, Constraints_top, Constraints_in_with_dups),

	% This removing of dups may or may not be useful: if they aren't
	% removed, there will be a lot of duplicates.
	list__sort_and_remove_dups(Constraints_in_with_dups, Constraints_in),

	Constr_info_in = constr_info(Map_prev, Varset_prev, Zeros_prev, 
								Constraints_in),
	traverse_disj_acc(Goals, Params, Disj_constraints1, 
		Disj_constraints, Constr_info_in, Constr_info_final, IO1, IO).


%-----------------------------------------------------------------------------


derive_nonneg_eqns(Bimap, NonNegs) :-
	bimap__coordinates(Bimap, Sizevars),
	Make_nonneg_eqn = lambda([Size::in, Eqn::out] is det, (
		Eqn = eqn([Size-one],(>=), zero)
	)),
	list__map(Make_nonneg_eqn, Sizevars, NonNegs).

%-----------------------------------------------------------------------------

% info_to_eqn : Takes some info about a unification and appends to the
% current constraints the
% equation that that corresponds to it.  Used for deconstruction and 
% construction unifications.  i.e. for a unification of the form
% X = f(U,V,W), if the functor norm counts the first and
% second arguments, the equation returned is |X| - |U| - |V| = |f|.
% This predicate fails when called for higher-order unifications.

:- pred info_to_eqn(var, cons_id, list(var), list(uni_mode), traversal_params, 
				constraint_info, constraint_info).
:- mode info_to_eqn(in, in, in, in, in, in, out) is semidet.
info_to_eqn(Var, ConsId, ArgVars0, Modes, Params, Constr_info0, Constr_info) :-

	params_get_functor_info(Params, FunctorInfo),
	params_get_var_types(Params, VarTypes),	
	map__lookup(VarTypes, Var, Type),
	
	params_get_module_info(Params, Module),

	\+ type_is_higher_order(Type, _, _),
	( type_to_type_id(Type, TypeId, _) ->
		functor_norm(FunctorInfo, TypeId, ConsId, Module, 
			Const, ArgVars0, CountedVars, Modes, _) 

		%So eqn is Var = Const + sum(CountedVars).
	
	;
		error("variable type in traverse_goal_2")	
	),
	
	( zero_size_type(Type, Module) ->
		new_zero_var(Var, Constr_info0, Constr_info1),
		First_coeff = []
	;
		rename_var(Var, NewVar, Constr_info0, Constr_info1),
		First_coeff = [NewVar-rat(1,1)]
	),

	Add_coeff = lambda([Var1::in, Coeffs0::in, Coeffs1::out, 
					C_i1::in, C_i2::out] is det, (
		map__lookup(VarTypes, Var1, Type1),
		( zero_size_type(Type1, Module) ->
			new_zero_var(Var1, C_i1, C_i2),
			Coeffs1 = Coeffs0
		;
			rename_var(Var1, Nvar, C_i1, C_i2),
			Coeffs1 = [Nvar-rat(-1,1) | Coeffs0]
		)
	)),

	list__foldl2(Add_coeff, CountedVars, First_coeff, 
					Coeffs, Constr_info1, Constr_info2),

	Constr_info2 = constr_info(Map, Varset, Zeros, Constraints),

	( Coeffs = [] ->
		( Const = 0 ->
			NewConstraints = Constraints
		;
			% if all the relevant variables have zero size type,
			% a linear combination of them must be zero.
			error("term_traversal2: error in calculating
			equation")
		)
	;
		NewConstraints = [eqn(Coeffs,(=),rat(Const,1)) | Constraints]
	),	
	Constr_info = constr_info(Map, Varset, Zeros, NewConstraints).


% simple_info_to_eqn : Takes some info about a unification and appends the
% equation that corresponds to it.  Used for assignment and simple_test
% unifications.  i.e. for a unification of the form X = Y,
% the equation returned is |X| - |Y| = 0.
:- pred simple_info_to_eqn(var, var, traversal_params, constraint_info, 
							constraint_info).
:- mode simple_info_to_eqn(in, in, in, in, out) is det.

simple_info_to_eqn(LVar, RVar, Params, Constr_info0, Constr_info) :-

	params_get_module_info(Params, Module),
	params_get_var_types(Params, VarTypes),

	map__lookup(VarTypes, LVar, LVarType),
	map__lookup(VarTypes, RVar, RVarType),

	( zero_size_type(LVarType, Module), zero_size_type(RVarType, Module) ->

		new_zero_var(LVar, Constr_info0, Constr_info1),
		new_zero_var(RVar, Constr_info1, Constr_info)
	;
		( (zero_size_type(LVarType, Module);
				zero_size_type(RVarType, Module)) ->
			error("Unification of two variables of different types")
		;
			rename_var(LVar, NewLvar, Constr_info0, Constr_info1),
			rename_var(RVar, NewRvar, Constr_info1, Constr_info2),

			Constr_info2 = constr_info(Map, Varset, Zeros, 
								Constraints),
			Eqn = eqn([NewLvar-rat(1,1), NewRvar-rat(-1,1)], (=), 
									zero),
			Constr_info = constr_info(Map, Varset, Zeros, 
							[Eqn|Constraints])
		)
	).



% Because quantification returns a conservative estimate of nonlocal
% vars, this returns a list of local vars which may omit some of 
% the real local vars.  #### This may be a problem!
:- pred get_local_vars(hlds_goal, list(var)).
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

:- pred compose_bijections(list(size_var), list(var), bimap(var, size_var), 
			bimap(size_var, size_var), bimap(size_var, size_var)).
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
			error("term_traversal2: size vars not unique")
		)
	;
		% We expect that type-info variables won't be in the map.
		% Nor will variables of types whose sizes are always zero.
		% That's fine, as long as they don't turn up in the equations,
		% (which they shouldn't, for exactly the same reason that they
		% aren't in the map).
		compose_bijections(Args, Headvars, HeadToSizeVarMap,
						SizeVarMap0, SizeVarMap)
	).
%-----------------------------------------------------------------------------

:- pred rename_vars_params(list(var), list(size_var), traversal_params, 
					constraint_info, constraint_info).
:- mode rename_vars_params(in, out, in, in, out) is det.
rename_vars_params(Vars, SizeVars, Params, Constr_info0, Constr_info) :-
	params_get_module_info(Params, Module),
	params_get_var_types(Params, VarTypes),
	rename_vars(Vars, SizeVars, Module, VarTypes, Constr_info0,
								Constr_info).

%-----------------------------------------------------------------------------

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
                        pred_proc_id,   % The procedure we are tracing through.
                        term__context,  % The context of the procedure.
			map(var, type)
		). 


term_traversal2__init_traversal_params(ModuleInfo, FunctorInfo, PredProcId,
		Context, VarTypeMap, Params) :-
        Params = traversal_params(ModuleInfo, FunctorInfo, PredProcId, Context,						VarTypeMap).

:- pred params_get_module_info(traversal_params::in, module_info::out)
        is det.
:- pred params_get_functor_info(traversal_params::in, functor_info::out)
        is det.
:- pred params_get_ppid(traversal_params::in, pred_proc_id::out)
        is det.
:- pred params_get_context(traversal_params::in, term__context::out)
        is det.
:- pred params_get_var_types(traversal_params::in, map(var,type)::out)
        is det.

params_get_module_info(Params, A) :-
        Params = traversal_params(A, _, _, _, _).

params_get_functor_info(Params, B) :-
        Params = traversal_params(_, B, _, _, _).

params_get_ppid(Params, C) :-
        Params = traversal_params(_, _, C, _, _).

params_get_context(Params, D) :-
        Params = traversal_params(_, _, _, D, _).

params_get_var_types(Params, E) :-
        Params = traversal_params(_, _, _, _, E).
