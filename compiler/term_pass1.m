%-----------------------------------------------------------------------------
%
% Copyright (C) 1997 University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------
%
% term_pass1.m
% Main author: crs.
%
% This file contains the first pass of the termination analysis.
% It sets the termination constant for all procedures, and also sets the
% terminates value for some procedures. (eg if the pred contains higher
% order arguments or calls.)
%
% The first pass processes each SCC in turn, following the dependency
% ordering given by hlds_dependency_info_get_dependency_ordering/2.
% The termination constant is set by first generating a list of
% constraints.  This list of constraints will contain one variable for each
% procedure in the SCC that is currently being processed.  After the
% complete set of constraints have been created, they are then solved using
% lp_solve.  As there is a single variable associated with each procedure,
% each variable is named using the pred_proc_id of the relevant procedure.
% Therefore, in some places in the program (eg term_pass1__equation), the
% pred_proc_id is actually referring to the variable associated with that
% procedure which still needs to be solved.
% 			
%-----------------------------------------------------------------------------
%

:- module term_pass1.

:- interface.

:- import_module io, hlds_module.

% This is the top level predicate of term_pass1.  It processes all of the
% procedures in the module, and sets the termination constant of each of
% them.  The procedures are processed in the order given by
% hlds_dependency_info_get_dependency_ordering.
:- pred proc_inequalities(module_info, module_info, io__state, io__state).
:- mode proc_inequalities(in, out, di, uo) is det.

%------------------------------------------------------------------------------

:- implementation.

:- import_module term_util, hlds_pred, hlds_goal, hlds_data, int, bag.
:- import_module term_errors, list, require, bool, std_util, char, map, string.
:- import_module mode_util, type_util.

%------------------------------------------------------------------------------

% This section contains proc_inequalities and its supporting functions.
% proc_inequalities goes through the dependency ordering, applying 
% goal_inequality to each SCC in turn.  goal_inequality returns a set of 
% constraints which are then solved using lp_solve.

% term_pass1__equation stores a single constraint.
% The constraint is of the form:
% pred_proc_id - list(pred_proc_id) >= term_util__constant
% Where pred_proc_id represents a variable which relates the total size of
% the input variables to the total size of the output variables.
:- type term_pass1__equation
	---> 	eqn(term_util__constant, pred_proc_id, list(pred_proc_id)).

:- type used_args == map(pred_proc_id, list(bool)).

proc_inequalities(Module0, Module) -->
	{ module_info_dependency_info(Module0, DependencyInfo) },
	{ hlds_dependency_info_get_dependency_ordering(DependencyInfo, 
		DependencyOrdering) },

	proc_inequalities_2(Module0, DependencyOrdering, Module).	


:- pred proc_inequalities_2(module_info, dependency_ordering, 
	module_info, io__state, io__state).
:- mode proc_inequalities_2(in, in, out, di, uo) is det.
proc_inequalities_2(Module, [], Module) --> [].
proc_inequalities_2(Module0, [ SCC | SCCs ], Module) -->
	{ init_used_args(Module0, SCC, InitUsedArgs) },
	proc_inequalities_3(Module0, SCC, SCC - InitUsedArgs, InitUsedArgs, 
		[], Module2),
	proc_inequalities_2(Module2, SCCs, Module).

% this is passed the same list of pred_proc_ids as the 2nd and 3rd
% arguments.  The first list is used for recursion.  The second list is
% used in the base case, as the base case needs to know which procedures it
% is processing.
:- pred proc_inequalities_3(module_info, list(pred_proc_id), 
	pair(list(pred_proc_id), used_args), used_args,
	list(term_pass1__equation), module_info, io__state, io__state).
:- mode proc_inequalities_3(in, in, in, in, in, out, di, uo) is det.
proc_inequalities_3(Module0, [], SCC - OldUsedArgs, NewUsedArgs, 
		Offs0, Module) --> 
	% First check used_args.  If a fixed point has been reached, then 
	% continue with the analysis and solve the resulting constraints.  
	% If a fixed point has not been reached, then recurse on the new
	% used args.
	( { OldUsedArgs = NewUsedArgs } ->
		% A fixed pointhas been reached.  Set used_args, then
		% process the constraints that have been created.
		{ module_info_preds(Module0, PredTable0) },
		{ set_used_args(PredTable0, SCC, NewUsedArgs, PredTable) },
		{ module_info_set_preds(Module0, PredTable, Module1) },

		% Solve the equations that have been created.
		{ proc_inequalities_3_remove_useless_offsets(Offs0, Offs, 
			Succ) },

		% XXX what is the correct context to use when referring to
		% a whole SCC?
		( { SCC = [proc(PredId, _)] } ->
			{ module_info_pred_info(Module0, PredId, PredInfo) },
			{ pred_info_context(PredInfo, Context) }
		;
			{ term__context_init(Context) }
		),
		( { Succ = no } ->
			% There is a directly recursive call where the
			% variables grow between the head and recursive
			% call.  Therefore the output is infinitly larger
			% than the input.  
			% e.g. foo(A) :- foo([1|A]).
			{ set_pred_proc_ids_const(SCC, inf(no), Module1, 
				Module) }
		; { Offs = [] } ->
			% There are no equations in this SCC
			% This has 2 possible causes.  If the predicate has
			% no output arguments, then the relative size of
			% input and output arguments is undefined.  If
			% there are no output arguments, then there will be
			% no equations created.  The other possibility is
			% that the procedure is a builtin predicate,  which
			% has an empty body.
	
			{ NewConst = inf(yes(Context - no_eqns)) },
			{ set_pred_proc_ids_const(SCC, NewConst,
				Module1, Module) } 
		;
			solve_eqns(Offs, SCC, Soln),

			% The equations have been solved, now put the
			% results into the module_info.
			( { Soln = solved(SolutionList) } ->
				% The solver successfully solved the
				% constraints.
				% PredTable0 and PredTable are used at the
				% start of this predicate.
				{ module_info_preds(Module1, PredTable1) },
				{ proc_inequalities_set_module(SolutionList, 
					PredTable1, PredTable2) },
				{ module_info_set_preds(Module1, PredTable2, 
					Module) }
			; { Soln = optimal } ->
				% All 'optimal' results should have been
				% changed into a list of solutions in
				% solve_eqns.  
				{ error("term_pass1__proc_inequalities_3: Unexpected Value\n")},
				{ Module1 = Module }
			;
				% The constraint solver failed to solve the
				% set of constraints - set the termination
				% constant to infinity.
				{ Error = Context - lpsolve_failed(Soln) },
				{ set_pred_proc_ids_const(SCC, 
					inf(yes(Error)), Module1, Module) }
			)
		)
	;
		% The analysis has not reached a fixed point, so recurse.
		proc_inequalities_3(Module0, SCC, SCC - NewUsedArgs, 
			NewUsedArgs, [], Module)
	).

proc_inequalities_3(Module0, [PPId | PPIds], SCC - OldUsedArgsMap, 
		UsedArgsMap0, Offs0, Module) -->
	{ PPId = proc(PredId, ProcId) },
	{ module_info_pred_proc_info(Module0, PredId, ProcId, _PredInfo, 
		ProcInfo) },
	{ proc_info_termination(ProcInfo, Termination) },

	( { Termination = term(not_set, _, _, _) } ->
		{ goal_inequality(Module0, PredId, ProcId, Offs1, Res, 
			OldUsedArgsMap, NewUsedArgs) },
		( { Res = error(Error) } ->
			% goal_inequality failed, so set all the
			% termination constants to infinity.
			{ set_pred_proc_ids_const(SCC, inf(yes(Error)), 
				Module0, Module2) },
			( 
				{ (
			 	Error = _ - horder_call
				; Error = _ - horder_args(_)
				) }
			->
				do_ppid_check_terminates(SCC, yes(Error), 
					Module2, Module)
			;
				{ Module = Module2 }
			)
		;
			{ list__append(Offs0, Offs1, Offs) },
			{ map__det_update(UsedArgsMap0, PPId, NewUsedArgs, 
				UsedArgsMap) },
			proc_inequalities_3(Module0, PPIds, 
				SCC - OldUsedArgsMap,
				UsedArgsMap, Offs, Module) 
		)
	;
		% The termination constant has already been set - hopefully
		% this is true of all the procedures in this SCC.  Perhaps
		% it would be wise to add a check that this is the case.
		{ Module = Module0 }
	).
	
% This procedure removes offsets where there are no variables in the offset.
% It would be nice if lp_solve would accept constraints of the form 
% (0 >= -1), but it doesnt so they need to be removed manually, which is
% what this procedure does. If this procedure returns `no' then the
% constraints are unsatisfiable (0 >= 1).  If the return value is `yes' the
% the constraints that were removed were all satisfiable.
:- pred proc_inequalities_3_remove_useless_offsets(
	list(term_pass1__equation), list(term_pass1__equation), bool).
:- mode proc_inequalities_3_remove_useless_offsets(in, out, out) is det.
proc_inequalities_3_remove_useless_offsets([], [], yes).
proc_inequalities_3_remove_useless_offsets([ Off0 | Offs0 ], Offs, Succ) :-
	( Off0 = eqn(Const, PPId, [ PPId ]) ->
		% in this case there is direct recursion
		( 
			(
				Const = set(Int),
				Int > 0
			;
				Const = inf(_)
			)
		->
			% in this case the recursive call is with larger
			% variables.  Hence the output could be unbounded
			Succ = no,
			Offs = Offs0
		;
			proc_inequalities_3_remove_useless_offsets(Offs0, 
				Offs, Succ)
		)
	;
		proc_inequalities_3_remove_useless_offsets(Offs0, Offs1, Succ),
		Offs = [ Off0 | Offs1]
	).

% This predicate takes the results from solve_eqns (if it successfully
% solved the constraints), and inserts these results into the
% predicate_table.
:- pred proc_inequalities_set_module(list(pair(pred_proc_id, int)),
	pred_table, pred_table).
:- mode proc_inequalities_set_module(in, in, out) is det.
proc_inequalities_set_module([], PredTable, PredTable). 
proc_inequalities_set_module([ Soln | Solns ], PredTable0, PredTable) :-
	Soln = PPId - Int,
	Const = set(Int),
	PPId = proc(PredId, ProcId),

	map__lookup(PredTable0, PredId, PredInfo),
	pred_info_procedures(PredInfo, ProcTable),
	map__lookup(ProcTable, ProcId, ProcInfo),

	proc_info_termination(ProcInfo, term(Const0, B, C, D)),
	( Const0 = not_set ->
		proc_info_set_termination(ProcInfo, term(Const, B, C, D), 
			ProcInfo1)
	;
		% This can only happen if an imported pred was in the same
		% SCC as some local preds, or if somehow some equations
		% were made for an imported pred.  Both of these occurances
		% represent an error in the code.
		error("term_pass1__proc_inequalities_set_module: Error"),
		ProcInfo1 = ProcInfo
	),
	map__set(ProcTable, ProcId, ProcInfo1, ProcTable1),
	pred_info_set_procedures(PredInfo, ProcTable1, PredInfo1),
	map__set(PredTable0, PredId, PredInfo1, PredTable1),
	proc_inequalities_set_module(Solns, PredTable1, PredTable).

% used to initialise the used_args map.
:- pred init_used_args(module_info, list(pred_proc_id), used_args).
:- mode init_used_args(in, in, out) is det.
init_used_args(_Module, [], InitMap) :-
	map__init(InitMap).
init_used_args(Module, [PPId | PPIds], Out) :-
	init_used_args(Module, PPIds, Out0),
	PPId = proc(PredId, ProcId),
	module_info_pred_proc_info(Module, PredId, ProcId, _, ProcInfo),
	proc_info_headvars(ProcInfo, HeadVars),
	term_util__make_bool_list(HeadVars, [], BoolList),
	map__det_insert(Out0, PPId, BoolList, Out).

% used to insert the information in the used_args map into the pred_table.
:- pred set_used_args(pred_table, list(pred_proc_id), used_args, pred_table).
:- mode set_used_args(in, in, in, out) is det.
set_used_args(PredTable, [], _, PredTable).
set_used_args(PredTable0, [PPId | PPIds], UsedArgsMap, PredTable) :-
	PPId = proc(PredId, ProcId),
	map__lookup(PredTable0, PredId, PredInfo0),
	pred_info_procedures(PredInfo0, ProcTable0),
	map__lookup(ProcTable0, ProcId, ProcInfo0),
	proc_info_termination(ProcInfo0, Term0),
	map__lookup(UsedArgsMap, PPId, UsedArgs),
	Term0 = term(Const, Terminates, _UsedArgs, MaybeError),
	Term = term(Const, Terminates, yes(UsedArgs), MaybeError),
	proc_info_set_termination(ProcInfo0, Term, ProcInfo),
	map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable),
	pred_info_set_procedures(PredInfo0, ProcTable, PredInfo),
	map__det_update(PredTable0, PredId, PredInfo, PredTable1),
	set_used_args(PredTable1, PPIds, UsedArgsMap, PredTable).
	

%-----------------------------------------------------------------------------%
% This section contains goal_inequality and its supporting functions.
% goal_inequality processes a goal, and finds an inequality relating the
% sizeof(input arguments) to the sizeof(output arguments).  If it finds a
% valid inequality, then it returns the offset of the inequality (with Res
% set to ok).  If no inequality can be found, then goal_inequality returns
% Res = error().

:- type goal_inequality_equ == list(pair(term_pass1__equation, bag(var))).
:- type goal_inequality_info == pair(functor_algorithm, used_args).
%	goal_inequality_info == UnifyInfo - CallInfo

:- pred goal_inequality(module_info, pred_id, proc_id,
	list(term_pass1__equation), term_util__result(term_errors__error), 
	used_args, list(bool)).
:- mode goal_inequality(in, in, in, out, out, in, out) is det.

goal_inequality(Module, PredId, ProcId, Offs, Res, OldUsedArgsMap, 
		NewUsedArgs):-
	module_info_pred_proc_info(Module, PredId, ProcId, PredInfo, ProcInfo),
	proc_info_headvars(ProcInfo, Args),
	proc_info_argmodes(ProcInfo, ArgModes),
	proc_info_goal(ProcInfo, GoalExpr - GoalInfo),

	partition_call_args(Module, ArgModes, Args, InVars, OutVars),
	bag__from_list(InVars, InVarsBag),
	bag__from_list(OutVars, OutVarsBag),

	PPId = proc(PredId, ProcId),
	InitEqn = eqn(set(0), PPId, []),
	% XXX the functor algorithm should be set at the command line.
	UnifyInfo = total,
	CallInfo = OldUsedArgsMap,
	Info = UnifyInfo - CallInfo,
	goal_inequality_2(GoalExpr, GoalInfo, Module, Info, PPId, 
		Res1, [ InitEqn - OutVarsBag ], OffsVars), 
	split_offs_vars(OffsVars, Offs, InVars2Bag),

	( Res1 = ok ->
		( bag__is_subbag(InVars2Bag, InVarsBag) ->
			map__lookup(OldUsedArgsMap, PPId, OldUsedArgs),
			goal_inequality_used_args(Args, InVars2Bag, OldUsedArgs,
				NewUsedArgs),
			Res = ok
		;
			pred_info_context(PredInfo, Context),
			% If Res is error(), then The Used Args should not
			% matter
			NewUsedArgs = [],
			Res = error(Context - 
				not_subset(InVars2Bag, InVarsBag))
		)
	;
		NewUsedArgs = [],
		Res = Res1
	).

:- pred goal_inequality_used_args(list(var), bag(var), list(bool), list(bool)).
:- mode goal_inequality_used_args(in, in, in, out) is det.
goal_inequality_used_args([], _InVarsBag, [], []).
goal_inequality_used_args([_ | _], _InVarsBag, [], []) :-
	error("term_pass1__goal_inequality_used_args: Unmatched variables").
goal_inequality_used_args([], _InVarsBag, [_ | _], []) :-
	error("term_pass1:goal_inequality_used_args: Unmatched variables").
goal_inequality_used_args([ Arg | Args ], InVarsBag, 
		[ OldUsedArg | OldUsedArgs ], [ UsedArg | UsedArgs ]):-
	( bag__contains(InVarsBag, Arg) ->
		UsedArg = yes
	;
		UsedArg = OldUsedArg	% This guarantees monotonicity
	),
	goal_inequality_used_args(Args, InVarsBag, OldUsedArgs, UsedArgs).
 

% goal_inequality_2 fails if it cannot form an inequality.  i.e. if there are
% higher order calls, higher order arguments, or pragma-c-code with
% relevent output variables. The reason for checking for higher order
% arguments is that this traps calls to solutions, which would not
% otherwise be checked.

:- pred goal_inequality_2(hlds_goal_expr, hlds_goal_info, module_info, 
	goal_inequality_info, pred_proc_id, 
	term_util__result(term_errors__error),
	goal_inequality_equ, goal_inequality_equ).
:- mode goal_inequality_2(in, in, in, in, in, out, in, out) is det.

goal_inequality_2(conj([]), _, _Module, _, _PPId, ok, Offs, Offs).
goal_inequality_2(conj([ Goal | Goals ]), _GoalInfo, Module, Info, 
	PPId, Res, Offs0, Offs) :-

	goal_inequality_2_conj(Goal, Goals, Module, Info, PPId, 
		Res, Offs0, Offs).

% This clause fails (returns Res=error()) if:
%	The called predicate contains higher order arguments
%	The terminates value of the called predicate is 'dont_know'
%	The termination constant of the called predicate is infinite
goal_inequality_2(call(CallPredId, CallProcId, Args, _IsBuiltin, _, _SymName),
		GoalInfo, Module, Info, PPId, Res, Offs0, Offs) :-
	module_info_pred_proc_info(Module, CallPredId, 
		CallProcId, _CallPredInfo, CallProcInfo),
	
	proc_info_argmodes(CallProcInfo, CallArgModes),

	partition_call_args(Module, CallArgModes, Args, InVars, OutVars),
	bag__from_list(OutVars, OutVarsBag),

	( goal_inequality_check_intersect(Offs0, OutVarsBag) ->
		% no intersection.
		Offs = Offs0,
		Res = ok
	;
		Info = _UnifyInfo - UsedArgsMap,
		CallPPId = proc(CallPredId, CallProcId),
		PPId = proc(PredId, ProcId),	
		module_info_pred_proc_info(Module, PredId, ProcId, _PredInfo, 
			ProcInfo),
		goal_info_get_context(GoalInfo, Context),
		proc_info_termination(CallProcInfo, CallTermination),
		CallTermination = term(CallTermConst, CallTerminates, 
			CallUsedArgs, _),
		proc_info_vartypes(ProcInfo, VarType),
		bag__from_list(InVars, InVarsBag0),
		( 
			CallUsedArgs = yes(UsedVars) 
		->
			remove_unused_args(InVarsBag0, Args, UsedVars,
				InVarsBag1)
		; %else if
			map__search(UsedArgsMap, CallPPId, UsedVars)
		->
			% In this case, it must be a mutually recursive call
			remove_unused_args(InVarsBag0, Args, UsedVars, 
				InVarsBag1)
		;
			InVarsBag1 = InVarsBag0
		),
		( CallTerminates = dont_know ->
			Res = error(Context - dont_know_proc_called(CallPPId)),
			Offs = Offs0
		; \+ check_horder_args(Args, VarType) ->
			Res = error(Context - horder_args(CallPPId)),
			Offs = Offs0
		;
			% If control reaches here, then there are no horder 
			% args, and the predcates termination property is
			% not dont_know.  Therefore modify the offsets.
			( 
				CallTermConst = not_set,
				Res = ok,
				Eqn = eqn(set(0), PPId, [CallPPId]),
				goal_inequality_modify_offs(InVarsBag1,
					OutVarsBag, Eqn, Offs0, Offs)
			; 
				CallTermConst = set(Int),
				Res = ok,
				Eqn = eqn(set(Int), PPId, []),
				goal_inequality_modify_offs(InVarsBag1,
					OutVarsBag, Eqn, Offs0, Offs)
			;
				CallTermConst = inf(_),
				Offs = Offs0,
				Res = error(Context - 
					inf_termination_const(CallPPId))
			)
		)
	).
	
goal_inequality_2(higher_order_call(_, _, _, _, _), 
		GoalInfo, _Module, _, _PPId, Error, Offs, Offs) :-
	goal_info_get_context(GoalInfo, Context),
	Error = error(Context - horder_call).

goal_inequality_2(switch(_SwitchVar, _CanFail, Cases, _StoreMap), GoalInfo,
		Module, Info, PPId, Res, Offs0, Offs) :-
	goal_inequality_2_switch(Cases, GoalInfo, Module, 
		Info, PPId, Res, Offs0, Offs).

goal_inequality_2(unify(_Var, _RHS, _UnifyMode, Unification, _UnifyContext),
		_GoalInfo, Module, Info, PPId, ok, Offs0, Offs) :-
	Info = FunctorAlg - _CallInfo,
	(
		Unification = construct(OutVar, ConsId, Args, UniModes),
		% Need to check if OutVar is a hgher order type.  If so,
		% return Offs unfodified.
		% XXX i am not sure that this is always valid.  If the
		% horder type is used elsewhere (eg in an argument to a
		% call), then it will be picked up there, and will return
		% Res = error(horder...). If this check is not made then
		% split_unification_vars can quit with an error, as
		% length(Args) is not necessarily equal to length(UniModes)
		% for higher order unifications.
		PPId = proc(PredId, ProcId),
		module_info_pred_proc_info(Module, PredId, ProcId,_, ProcInfo),
		proc_info_vartypes(ProcInfo, VarTypes),
		map__lookup(VarTypes, OutVar, Type),
		( type_is_higher_order(Type, _, _) ->
			Offs = Offs0
		;
			split_unification_vars(Args, UniModes, Module,
				InVarsBag , OutVarsBag),
			bag__insert(OutVarsBag, OutVar, OutVarsBag0),
			functor_norm(FunctorAlg, ConsId, Module, FunctorNorm),
			Eqn = eqn(set(FunctorNorm), PPId, []),
			goal_inequality_modify_offs(InVarsBag, OutVarsBag0,
				Eqn, Offs0, Offs)
		)
	;
		Unification = deconstruct(InVar, ConsId, Args, UniModes, _),
		split_unification_vars(Args, UniModes, Module,
			InVarsBag , OutVarsBag),
		bag__insert(InVarsBag, InVar, InVarsBag0),
		functor_norm(FunctorAlg, ConsId, Module, FunctorNorm),
		Eqn = eqn(set(- FunctorNorm), PPId, []),
		goal_inequality_modify_offs(InVarsBag0, OutVarsBag,
			Eqn, Offs0, Offs)
	;
		Unification = assign(OutVar, InVar),
		Eqn = eqn(set(0), PPId, []),
		bag__init(InitBag),
		bag__insert(InitBag, InVar, InVarBag),
		bag__insert(InitBag, OutVar, OutVarBag),
		goal_inequality_modify_offs(InVarBag, OutVarBag, Eqn, 
			Offs0, Offs)
	;
		Unification = simple_test(_InVar1, _InVar2),
		Offs = Offs0
	;
		Unification = complicated_unify(_, _),
		error("Unexpected complicated_unify in termination.m")
	).

% No variables are bound in an empty disjunction (fail), so it does not
% make sense to define an equation relating input variables to output
% variables.
goal_inequality_2(disj([], _), _, _Module, _, _PPId, ok, Offs, Offs).
goal_inequality_2(disj([ Goal | Goals ], _StoreMap), 
		GoalInfo, Module, Info, PPId, Res, Offs0, Offs) :-
	goal_inequality_2_disj(Goal, Goals, GoalInfo, Module, Info, 
		PPId, Res, Offs0, Offs).

% As we are trying to form a relationship between variables sizes, and no
% variables can be bound in a not, we dont need to evaluate inside the not
goal_inequality_2(not(_), _GoalInfo, _Module, _, _PPId, ok, Offs, Offs).

goal_inequality_2(some(_Vars, GoalExpr - GoalInfo), _, Module, Info, 
		PPId, Res, Offs0, Offs) :-
	goal_inequality_2(GoalExpr, GoalInfo, Module, Info, 
		PPId, Res, Offs0, Offs).
	
% an if-then-else is processed as:
% (
% 	if_goal,
% 	then_goal
% ;
% 	% the reason that there is no need for a not(if_goal) here is that
% 	% no variables are bound in a not.  If the in_goal is
% 	% non-terminating, then this will be discovered in when the if-then
% 	% goal is processed
% 	else_goal
% )
goal_inequality_2(if_then_else(_Vars, IfGoal, ThenGoal, ElseGoal, _StoreMap),
		GoalInfo, Module, Info, PPId, Res, Offs0, Offs) :-	
	NewThenGoal = conj([IfGoal, ThenGoal]) - GoalInfo,
	goal_inequality_2_disj(NewThenGoal, [ElseGoal], GoalInfo, Module, 
		Info, PPId, Res, Offs0, Offs). 

goal_inequality_2(pragma_c_code(_, _, CallPredId, CallProcId, Args, _, _), 
		GoalInfo, Module, _Info, _PPId, Res, Offs, Offs) :-

	module_info_pred_proc_info(Module, CallPredId, CallProcId, _,
		CallProcInfo),
	proc_info_argmodes(CallProcInfo, CallArgModes),
	partition_call_args(Module, CallArgModes, Args, _InVars, OutVars),
	bag__from_list(OutVars, OutVarBag),

	( goal_inequality_check_intersect(Offs, OutVarBag) ->
		% no intersection
		% c_code has no important output vars, so we need no error
		Res = ok
	;
		goal_info_get_context(GoalInfo, Context),
		Res = error(Context - pragma_c_code)
	).

%-----------------------------------------------------------------------------%

:- pred goal_inequality_2_conj(hlds_goal, list(hlds_goal), 
	module_info, goal_inequality_info, pred_proc_id,
	term_util__result(term_errors__error), goal_inequality_equ,
	goal_inequality_equ).
:- mode goal_inequality_2_conj(in, in, in, in, in, out, in, out) is det.

goal_inequality_2_conj(Goal, [], Module, Info, PPId, Res,
		Offs0, Offs) :-
	Goal = GoalExpr - GoalInfo,
	goal_inequality_2(GoalExpr, GoalInfo, Module, Info, 
		PPId, Res, Offs0, Offs).

goal_inequality_2_conj(Goal, [ Goal2 | Goals ], Module, Info, PPId, 
		Res, Offs0, Offs) :-
	goal_inequality_2_conj(Goal2, Goals, Module, Info, 
		PPId, Res1, Offs0, Offs1),
	( Res1 = ok ->
		Goal = GoalExpr - GoalInfo,
		goal_inequality_2(GoalExpr, GoalInfo, Module, Info, 
			PPId, Res, Offs1, Offs)
	;
		Res = Res1,
		Offs = Offs1
	). 

:- pred goal_inequality_2_switch(list(case), hlds_goal_info, 
	module_info, goal_inequality_info, pred_proc_id,
	term_util__result(term_errors__error), goal_inequality_equ,
	goal_inequality_equ).
:- mode goal_inequality_2_switch(in, in, in, in, in, out, in, out) is det.

goal_inequality_2_switch([], _, _Module, _, _PPId,
		ok, Offs, Offs) :-
	error("Unexpected empty switch").

goal_inequality_2_switch([ Case | Cases ], SwitchGoalInfo, 
	Module, Info, PPId, Res, Offs0, Offs) :-

	Case = case(_ConsId, Goal),
	Goal = GoalExpr - GoalInfo,	
	goal_inequality_2(GoalExpr, GoalInfo, Module, Info, 
		PPId, Res1, Offs0, Offs1),

	( Res1 = error(_) ->
		Res = Res1,
		Offs = Offs1
	; Cases = [] ->
		Res = Res1,
		Offs = Offs1
	;
		goal_inequality_2_switch(Cases, SwitchGoalInfo, 
			Module, Info, PPId, Res2, Offs0, Offs2),

		( Res2 = error(_) ->
			Res = Res2,
			Offs = Offs2
		;
			list__append(Offs1, Offs2, Offs),
			Res = ok
		)
	).
	
:- pred goal_inequality_2_disj(hlds_goal, list(hlds_goal), hlds_goal_info, 
	module_info, goal_inequality_info, pred_proc_id,
	term_util__result(term_errors__error), goal_inequality_equ,
	goal_inequality_equ).
:- mode goal_inequality_2_disj(in, in, in, in, in, in, out, in, out) is det.
goal_inequality_2_disj(Goal, [], _, Module, Info, PPId, 
		Res, Offs0, Offs) :-
	Goal = GoalExpr - GoalInfo,
	goal_inequality_2(GoalExpr, GoalInfo, Module, Info, 
		PPId, Res, Offs0, Offs).

goal_inequality_2_disj(Goal, [Goal2 | Goals], DisjGoalInfo, Module, 
			Info, PPId, Res, Offs0, Offs) :-
	goal_inequality_2_disj(Goal2, Goals, DisjGoalInfo, Module, 
		Info, PPId, Res1, Offs0, Offs1),

	Goal = GoalExpr - GoalInfo,
	goal_inequality_2(GoalExpr, GoalInfo, Module, Info, 
		PPId, Res2, Offs0, Offs2),

	( Res1 = error(_) ->
		Res = Res1,
		Offs = Offs1
	; Res2 = error(_) ->
		Res = Res2,
		Offs = Offs2
	;
		list__append(Offs1, Offs2, Offs),
		Res = ok
	).

		
%-----------------------------------------------------------------------------%
% support functions for goal_inequality

:- pred goal_inequality_modify_offs(bag(var), bag(var), term_pass1__equation,
	goal_inequality_equ, goal_inequality_equ).
:- mode goal_inequality_modify_offs(in, in, in, in, out) is det.
goal_inequality_modify_offs(_, _, _, [], []).
goal_inequality_modify_offs(InVars, OutVars, ModEqn, [Out0 | Out0s], 
		[Out | Outs ]) :-
	Out0 = Equation0 - Vars0,
	( bag__intersect(OutVars, Vars0) ->
		% there is an intersection
		bag__subtract(Vars0, OutVars, Vars1),
		bag__union(Vars1, InVars, Vars),
		eqn_add(ModEqn, Equation0, Equation),
		Out = Equation - Vars
	;
		Out = Out0
	),
	goal_inequality_modify_offs(InVars, OutVars, ModEqn, Out0s, Outs).

% adds two equations together
:- pred eqn_add(term_pass1__equation, term_pass1__equation,
	term_pass1__equation).
:- mode eqn_add(in, in, out) is det.
eqn_add(eqn(Const1, PPId1, PPList1), eqn(Const2, PPId2, PPList2), Out) :-
	( PPId1 = PPId2 ->
		( ( Const1 = not_set ; Const2 = not_set ) ->
			OutConst = not_set
		; ( Const1 = inf(_) ; Const2 = inf(_) ) ->
			OutConst = inf(no)
		; ( Const1 = set(Num1), Const2 = set(Num2)) ->
			OutNum = Num1 + Num2,
			OutConst = set(OutNum)
		;
			% This really cant happen, as Const1 and Const2 can 
			% only be (not_set ; inf ; set(int))
			% as the disjunction is not flattened, mercury cant
			% work it out, and would call the pred semidet
			error("Internal software error in termination.m\n")
		),
		list__append(PPList1, PPList2, OutPPList),
		Out = eqn(OutConst, PPId1, OutPPList)
	;
		% it makes no sense to add equations with different PPId
		% values.  Its like trying to add apples to oranges
		error("term_pass1:eqn_add was called with illegal arguments\n")
	).

:- pred goal_inequality_check_intersect(goal_inequality_equ, bag(var)).
:- mode goal_inequality_check_intersect(in, in) is semidet.
% succeeds if there is no intersection.
goal_inequality_check_intersect([], _).
goal_inequality_check_intersect([ Out | Outs ], OutVarBag) :-
	Out = _Equation - OutBag,
	\+ bag__intersect(OutBag, OutVarBag),
	goal_inequality_check_intersect(Outs, OutVarBag).


% This function takes the list of pair(equation, bag(var)), and splits it
% up into a list(equation) and a bag(var).  The output bag(var) is given by
% taking the least-upper-bound of each of the bags in the initial list.
% The least upper bound is the smallest multiset such that each bag in the
% initial list is a subset of the least upper bound.
:- pred split_offs_vars(goal_inequality_equ, list(term_pass1__equation),
	bag(var)).
:- mode split_offs_vars(in, out, out) is det.
split_offs_vars([], [], InitBag) :-
	bag__init(InitBag).
split_offs_vars([ X | Xs ], [ Off | Offs ], VarBag) :-
	split_offs_vars(Xs, Offs, Bag0),
	X = Off - SubBag,
	% now need to produce the least upper bound of Bag0 and SubBag
	% eg. need least upper bound of {1, 1, 2, 2, 3 }, {1, 1, 2, 3, 3, 3}
	% bag__subtract({1, 1, 2, 2, 3 }, {1, 1, 2, 3, 3, 3}, {2}),
	% bag__union({1, 1, 2, 3, 3, 3}, {2}, {1, 1, 2, 2, 3, 3, 3}).
	% and {1, 1, 2, 2, 3, 3, 3} is the correct least upper bound
	bag__subtract(Bag0, SubBag, Bag1),
	bag__union(Bag1, SubBag, VarBag).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
% Solve the list of constraints 

% output is of the form required by lp_solve.
% which is given the input = [eqn(Const, PPid, [PPidList])]
% max: .......
% c1: PPid - (PPidList) > Const;
% c2: PPid - (PPidList) > Const;
% where PPid (proc(PredId, ProcId)) is printed as ' aPredId_ProcId - b '
% The choice of the letter `a' is arbitrary, and is chosen as lp_solve does
% not allow variables to start with digits.
% The variable `b' is used as lp_solve will only solve for positive values
% of variables.  replacing each variable occurance with ` a#_# - b ', this
% avoids the problem of only allowing positive variables as  a#_# - b can
% be negative even when a#_# and b are both positive.
%

:- pred solve_eqns(list(term_pass1__equation), list(pred_proc_id), eqn_soln,
	io__state, io__state).
:- mode solve_eqns(in, in, out, di, uo) is det.

solve_eqns(Equations, PPIds, Soln) -->
	io__progname_base("term_pass1.m", ProgName),
	io__tmpnam(ConstraintFile),
	io__tmpnam(OutputFile),
	
	solve_eqns_constraint_file(Equations, PPIds, ConstraintFile,
		ConstraintSucc),

	( { ConstraintSucc = yes } ->
		% run lp_solve
		io__get_environment_var("MERCURY_LPSOLVE", Lpsolve0),
		( { Lpsolve0 = yes(Lpsolve1) } ->
			{ Lpsolve = Lpsolve1 }
		;
			{ Lpsolve = "lp_solve" }
		),
		{ string__append_list([
			Lpsolve,
			" <",
			ConstraintFile,
			" > ",
			OutputFile], Command) },
	
		io__call_system(Command, Res0),
		% Test the return value
		( 
			{ Res0  = ok(RetVal) },
			{ lpsolve_ret_val(RetVal, Result) },
			( { Result = optimal } ->
				% Wohoo, lp_solve worked out an answer!!
				solve_eqns_output_file(OutputFile, Soln0)
				/*******
				% Tests to see if lp_solve managed to solve
				% the constraints.  If lp_solve fails, it
				% is sometimes useful in debugging to see
				% the file that forced lp_solve to fail.
				( { Soln0 = solved(_) } ->
					[]
				;

					io__write_string("solve_eqns_parse_output_file failed on the following file:\n"),
					{ string__append_list([
						"cat ",
                				OutputFile,
						" ",
						ConstraintFile], Command1) },
        				io__call_system(Command1, _RetVal),
					io__write_string("----------- end of file --------\n")
				)
				******/
			;
				% lp_solve failed to solve the constraints.
				% This could be for a number of reasons,
				% and the value of Result will represent
				% the reason.

				/****
				io__write_string("lp_solve failed on the following input file:\n"),
				{ string__append_list([
					"cat ",
					ConstraintFile], Command1) },
        			io__call_system(Command1, _RetVal),
				io__write_string("----------- end of file --------\n"),
				*****/
				{ Soln0 = Result }
			)
		;
			{ Res0 = error(Error0) },
			{ io__error_message(Error0, Msg0) },
			io__write_strings([
				ProgName,
				": Error with system call `",
				Command,
				"' : ",
				Msg0,
				"\n" ]),
			io__set_exit_status(1),
			{ Soln0 = fatal_error }
		),

		% Remove and close all temporary files.
		io__remove_file(ConstraintFile, Res1),
		( { Res1 = error(Error1) } ->
			{ io__error_message(Error1, Msg1) },
			io__write_strings([
				ProgName,
				": Error unlinking temporary file `",
				ConstraintFile,
				"' : ",
				Msg1,
				"\n" ]),
			io__set_exit_status(1),
			{ Soln1 = fatal_error }
		;
			{ Soln1 = Soln0 } 
		),
		io__remove_file(OutputFile, Res2),
		( { Res2 = error(Error2) } ->
			{ io__error_message(Error2, Msg2) },
			io__write_strings([
				"Error unlinking temporary file `",
				OutputFile,
				"' : ",
				Msg2,
				"\n" ]),
			io__set_exit_status(1),
			{ Soln = fatal_error }
		;
			{ Soln = Soln1 }
		)
	;
		% Failed to create the constraint file.
		{ Soln = fatal_error }
	).

% This creates the constraint file, in a format suitable for lp_solve.
% This really shouldn't be called with Equations=[] as lp_solve exits with
% an error if it is called without any constraints.
:- pred solve_eqns_constraint_file(list(term_pass1__equation),
	list(pred_proc_id), string, bool, io__state, io__state).
:- mode solve_eqns_constraint_file(in, in, in, out, di, uo) is det.

solve_eqns_constraint_file(Equations, PPIds, ConstraintFile, Success) -->
	
	io__open_output(ConstraintFile, Res),
	( 	{ Res = error(Error) },
		% error message and quit
		io__progname_base("termination.m", ProgName),
		{ io__error_message(Error, Msg) },
	
		io__write_string(ProgName),
		io__write_string(": cannot open temporary file `"),
		io__write_string(ConstraintFile),
		io__write_string("' for output: "),
		io__write_string(Msg),
		io__write_string("\n"),
		io__set_exit_status(1),
		{ Success = no }
	;
		{ Res = ok(Stream) },
		( { Equations = [] } ->
			{ Success = no }
		;
			io__set_output_stream(Stream, OldStream),
			% create the constraint file
			output_eqns(Equations, PPIds, Success),
	
			io__set_output_stream(OldStream, _),
			io__close_output(Stream)
		)
	).

% Prepare to parse the output from lp_solve.
:- pred solve_eqns_output_file(string, eqn_soln, io__state, io__state).
:- mode solve_eqns_output_file(in, out, di, uo) is det.
solve_eqns_output_file(OutputFile, Soln) -->
	% Wohoo, lp_solve worked out an answer!!
	io__open_input(OutputFile, OutputRes),
	( 	{ OutputRes = error(Error) },
		io__progname_base("termination.m", ProgName),
		{ io__error_message(Error, Msg) },

		io__write_string(ProgName),
		io__write_string(": cannot open temporary file `"),
		io__write_string(OutputFile),
		io__write_string("' for input: "),
		io__write_string(Msg),
		io__write_string("\n"),
		io__set_exit_status(1),
		{ Soln = fatal_error }
	;
		{ OutputRes = ok(Stream) },
		io__set_input_stream(Stream, OldStream),
		% need to interpret it now
		solve_eqns_parse_output_file(Soln),
		io__set_input_stream(OldStream, _),
		io__close_input(Stream)
	).

% Parse the output from lp_solve.
:- pred solve_eqns_parse_output_file(eqn_soln, io__state, io__state).
:- mode solve_eqns_parse_output_file(out, di, uo) is det.
solve_eqns_parse_output_file(Soln) -->
	io__read_line(Res1),
	( { Res1 = ok(_) } ->
		solve_eqns_parse_output_file_2(Soln0, MaybeBVal),
		( { Soln0 = solved(Result0) } ->
			( { MaybeBVal = yes(BVal) } ->
				{ solve_eqns_output_file_2(Result0, BVal,
					Result) },
				{ Soln = solved(Result) }
			;
				io__write_string("no bval\n"),
				{ Soln = parse_error }
			)
		;
			io__write_string(
				"parse_output_file returned not solved\n"),
			{ Soln = parse_error }
		)
	;
		{ Soln = parse_error }
	).

:- pred solve_eqns_output_file_2(list(pair(pred_proc_id, int)), int,
	list(pair(pred_proc_id, int))).
:- mode solve_eqns_output_file_2(in, in, out) is det.
solve_eqns_output_file_2([], _, []). 
solve_eqns_output_file_2([X | Xs], BVal, [Y | Ys]) :-
	X = PPId - XVal, 	% pair deconstruction
	YVal = XVal - BVal,	% subtraction
	Y = PPId - YVal,	% pair construction
	solve_eqns_output_file_2(Xs, BVal, Ys).
		
:- pred solve_eqns_parse_output_file_2(eqn_soln, maybe(int), io__state,
	io__state).
:- mode solve_eqns_parse_output_file_2(out, out, di, uo) is det.
solve_eqns_parse_output_file_2(Soln, BVal) -->
	io__read_line(Res1),
	( { Res1 = ok([ X | Xs ]) } ->
		( 
			{ X = 'a' },
			{ char_list_remove_int(Xs, PredInt, Xs1) },
			{ Xs1 = [ '_' | Xs2 ] },
			{ char_list_remove_int(Xs2, ProcInt, Xs3) },
			{ char_list_remove_whitespace(Xs3, Xs4) },
			{ char_list_remove_int(Xs4, Value, _Xs5) }
		->
			% have found a soln
			{ pred_id_to_int(PredId, PredInt) },
			{ proc_id_to_int(ProcId, ProcInt) },
			solve_eqns_parse_output_file_2(Soln0, BVal),
			( { Soln0 = solved(SolnList) } ->
				{ NewSoln = proc(PredId, ProcId) - Value },
				{ Soln = solved([NewSoln | SolnList ]) }
			;
				{ Soln = Soln0 }
			)
		; 
			{ X = 'b' },
			{ char_list_remove_whitespace(Xs, Xs1) },
			{ char_list_remove_int(Xs1, Value, _Xs2) }
		->
			solve_eqns_parse_output_file_2(Soln, _Bval),
			{ BVal = yes(Value) }
		;
			{ Soln = parse_error },
			{ BVal = no }
		)
	; { Res1 = eof } ->
		{ Soln = solved([]) },
		{ BVal = no }
	;
		{ Soln = parse_error },
		{ BVal = no }
	).

:- pred char_list_remove_int(list(char), int, list(char)).
:- mode char_list_remove_int(in, out, out) is semidet.
char_list_remove_int([X | Xs], Int, ListOut) :-
	char__is_digit(X),
	char__to_int(X, Int0),
	Int1 = Int0 - 48,   % char__to_int('0', 48).
	char_list_remove_int_2(Xs, Int1, Int, ListOut).

:- pred char_list_remove_int_2(list(char), int, int, list(char)).
:- mode char_list_remove_int_2(in, in, out, out) is semidet.

char_list_remove_int_2([], Int, Int, []).
char_list_remove_int_2([X | Xs], Int0, Int, ListOut) :-
	( char__is_digit(X) ->
		char__to_int(X, Int1),
		Int2 = Int0 * 10 + Int1 - 48,
		char_list_remove_int_2(Xs, Int2, Int, ListOut)
	;
		ListOut = [ X | Xs ],
		Int = Int0
	).
		
:- pred char_list_remove_whitespace(list(char), list(char)).
:- mode char_list_remove_whitespace(in, out) is det.
char_list_remove_whitespace([], []).
char_list_remove_whitespace([ X | Xs ], Out) :-
	( char__is_whitespace(X) ->
		char_list_remove_whitespace(Xs, Out)
	;
		Out = [ X | Xs ]
	).

:- pred lpsolve_ret_val(int, eqn_soln).
:- mode lpsolve_ret_val(in, out) is det.
% XXX The >> 8 is not portable, and needs to ba changed.
lpsolve_ret_val(Int0, Result) :-
	Int = Int0 >> 8,
	( Int = -1	->	Result = fatal_error
	; Int = 0	->	Result = optimal
	; Int = 2	->	Result = infeasible
	; Int = 3	->	Result = unbounded
	; 			Result = failure
	).

%-----------------------------------------------------------------------------%
% These predicates are used to output a list of equations in a form
% suitable for lp_solve.  
:- pred output_eqns(list(term_pass1__equation), list(pred_proc_id),
	bool, io__state , io__state).
:- mode output_eqns(in, in, out, di, uo) is det.

output_eqns(Xs, PPIds, Success) --> 
	% output: 'max: # b - PPIds'
	io__write_string("max: "),
	{ list__length(PPIds, Length) },
	io__write_int(Length),
	io__write_string(" b "),
	output_eqn_2(PPIds),
	io__write_string(";\n"),

	output_eqns_2(Xs, 1, Success).

:- pred output_eqns_2(list(term_pass1__equation), int,
	bool, io__state , io__state).
:- mode output_eqns_2(in, in, out, di, uo) is det.

output_eqns_2([], _Count, yes) --> [].
output_eqns_2([ X | Xs ], Count, Succ) --> 
	output_eqn(X, Count, Succ0),
	( { Succ0 = yes } ->
		{ Count1 is Count + 1 },
		output_eqns_2(Xs, Count1, Succ)
	;
		{ Succ = Succ0 }
	).


:- pred output_eqn(term_pass1__equation, int, bool, io__state,
	io__state).
:- mode output_eqn(in, in, out, di, uo) is det.

% each constraint is of the form:
% c#: # b + PPId - (PPIdList) > Const;
% each PPId is printed as `aPredId_ProcId'
% As each PPId can be negative, and lp_solve allows only positive
% variables, we introduce a dummy variable 'b' such that 
% Actual PPId value = returned PPId value - b, where the returned value is 
% always non-negative
output_eqn(Eqn, Count, Succ) -->
	{ Eqn = eqn(Const, PPId, PPIdList0) },
	( { list__delete_first(PPIdList0, PPId, PPIdList1) } ->
		{ Deleted = yes },
		{ PPIdList = PPIdList1 }
	;
		{ Deleted = no },
		{ PPIdList = PPIdList0 }
	),
	{ list__length(PPIdList, Length) },

	( 
		{ Length = 0 },
		{ Deleted = yes }
	->
		% nothing on the LHS of the constraint
		{ Succ = no}	% XXX is this correct, or should we return 
				% the fact that we didnt output a constraint
				% currently if we dont print out any constraints
				% then lp_solve fails.
	;
		( { Deleted = yes } ->
			{ Length1 = Length }
		;
			{ Length1 = Length - 1}
		),

		% output 'c#: '
		io__write_char('c'),
		io__write_int(Count),
		io__write_string(": "),
	
		% maybe output '# b '
		( { Length1 = 0 } ->
			[]
		;	
			io__write_int(Length1),
			io__write_string(" b ")
		),
		
		% maybe output ' + PPId'
		( { Deleted = yes } ->
			[]
		;
			io__write_string(" + a"),
			output_eqn_ppid(PPId)
		),

		% output 'PPIdList > Const;'
		output_eqn_2(PPIdList),

		io__write_string(" > "),
		( { Const = set(Int) } ->
			io__write_int(Int), 
			{ Succ = yes }
		;
			{ Succ = no }
		),
		io__write_string(";\n")
	).
	
% outputs each of the PPId's in the form: ' - aPredId_ProcId'
:- pred output_eqn_2(list(pred_proc_id), io__state, io__state).
:- mode output_eqn_2(in, di, uo) is det.

output_eqn_2([]) --> [].
output_eqn_2([ X | Xs ]) --> 
	io__write_string(" - a"),
	output_eqn_ppid(X),
	output_eqn_2(Xs).

% outputs a PPId in the form "PredId_ProcId"
:- pred output_eqn_ppid(pred_proc_id, io__state, io__state).
:- mode output_eqn_ppid(in, di, uo) is det.
output_eqn_ppid(proc(PredId, ProcId)) -->
	{ pred_id_to_int(PredId, PredInt) },
	{ proc_id_to_int(ProcId, ProcInt) },
	io__write_int(PredInt),
	io__write_char('_'),
	io__write_int(ProcInt).

