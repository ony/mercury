%-----------------------------------------------------------------------------
%
% Copyright (C) 1997 University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------
%
% term_pass2.m
% Main author: crs.
%
% This file contains the actual termination analysis.  This file goes
% through each procedure, and sets the terminates property of each one.
%
% Termination analysis:
% This goes through each of the SCC's in turn, analysing them to determine
% which predicates terminate.
% 			
%-----------------------------------------------------------------------------
:- module term_pass2.
:- interface.

:- import_module io, hlds_module.

:- pred termination(module_info, module_info, io__state, io__state).
:- mode termination(in, out, di, uo) is det.

:- implementation.

:- import_module bag, hlds_pred, std_util, int, list, relation, require.
:- import_module set, hlds_goal, term_util, term_errors, bool.
:- import_module globals, options, map, term.

% Used in termination_3_goal to keep track of the relative sizes of variables
% between the head of a pred and any recursive calls.
:- type termination_3
	--->	tuple(pred_proc_id, 	% The called procedure
			int, 		% The relative size of the active
					% variables, in comparison with the 
					% size of the variables in the
					% recursive call
			bag(var), 	% The bag of active variables.
			maybe(var), 	% Only for single argrgument analysis.
					% This stores which head variable
					% is being traced by this tuple.
			term__context).	% Where the call occured

termination(Module0, Module) -->
	{ module_info_dependency_info(Module0, DependencyInfo) },
	{ hlds_dependency_info_get_dependency_ordering(DependencyInfo, 
		DependencyOrdering) },

	termination_2(Module0, DependencyOrdering, Module).


:- pred termination_2(module_info, dependency_ordering, module_info, io__state,
	io__state).
:- mode termination_2(in, in, out, di, uo) is det.
termination_2(Module, [], Module) --> [].
termination_2(Module0, [SCC | SCCs], Module) -->
	termination_2_check_terminates(SCC, SCC, Module0, Module1, Succ),
	( { Succ = yes } ->
		% Need to run termination checking on this SCC.
		% Initialise the relation
		{ relation__init(Relation0) },
		% Add each procedure to the relation.
		{ add_pred_procs_to_relation(SCC, Relation0, Relation1) },
		% Analyse the current SCC.
		{ init_used_args(SCC, Module1, InitUsedArgs) },
		{ call_termination_3(SCC, Module1, Res, InitUsedArgs, 
			Relation1, Relation2) },
		( 	
			{ Res = ok },
			% Check that the relation returned is acyclic 
			% and set termination accordingly.
			( { relation__tsort(Relation2, _) } ->
				% All the procedures in this SCC terminate,
				% set all procedures to yes.
				{ set_pred_proc_ids_terminates(SCC, 
					yes, no, Module1, Module3) }
			;
				% Need to set all the procs to dont_know.
				( { SCC = [ proc(PredId, _) | _ ] } ->
					{ module_info_pred_info(Module1,
						PredId, PredInfo) },
					{ pred_info_context(PredInfo, 
						Context) }
				;
					{ term__context_init(Context) }
				),
				termination_3_single_args(SCC, 
					Context - not_dag, InitUsedArgs, 
					Module1, Module3)
			)
		;
			{ Res = error(Error) },
			termination_3_single_args(SCC, Error, InitUsedArgs, 
				Module1, Module3)
		)
	;
		% All the termination properties are already set.
		{ Module3 = Module1 }
	),
	% Recurse.
	termination_2(Module3, SCCs, Module).



% If this predicate returns Succ = yes, then termination analysis needs to be
% run on this SCC.  If it returns Succ =  no, then the termination
% properties of this SCC have already been set.
% XXX this can be improved.  If ANY Terminates in the SCC is set to dont_know,
% then the whole SCC can be set to dont_know
:- pred termination_2_check_terminates(list(pred_proc_id), list(pred_proc_id),
	module_info, module_info, bool, io__state, io__state).
:- mode termination_2_check_terminates(in, in, in, out, out, di, uo) is det.
termination_2_check_terminates([], _SCC, Module, Module, no) --> [].
termination_2_check_terminates([ PPId | PPIds ], SCC,Module0, Module, Succ) -->
	{ PPId = proc(PredId, ProcId) },
	{ module_info_pred_proc_info(Module0, PredId, ProcId, _, ProcInfo) },
	{ proc_info_termination(ProcInfo, Term) },
	{ Term = term(_Const, Terminates, _UsedArgs, MaybeError) },
	( 
		{ Terminates = not_set },
		{ Succ = yes },
		{ Module = Module0 }
	;
		{ Terminates = yes },
		termination_2_check_terminates(PPIds, SCC, Module0, 
			Module, Succ)
	;
		{ Terminates = dont_know},
		{ Succ = no },
		( { MaybeError = yes(Error) } ->
			do_ppid_check_terminates(SCC, Error, Module0, Module)
		;
			{ error("term_pass2.m: unexpected value in termination_2_check_terminates/6") }
		)
	).

% This predicate runs termination_3 until a fixed point for UsedArgs 
% is reached.
:- pred call_termination_3(list(pred_proc_id), module_info,
	term_util__result(term_errors__error), map(pred_proc_id, set(var)),
	relation(pred_proc_id), relation(pred_proc_id)).
:- mode call_termination_3(in, in, out, in, in, out) is det.
call_termination_3(SCC, Module, Result, UsedArgs0, Relation0, Relation) :-
	termination_3(SCC, Module, Res1, UsedArgs0, UsedArgs1, 
		Relation0, Relation1),
	( 
		% If some other error prevented the analysis from proving
		% termination, then finding a fixed point will not assist
		% in proving termination, so we may as well stop here.
		( Res1 = error(_ - not_subset(_, _, _))
		; Res1 = error(_ - positive_value(_, _))
		),
		UsedArgs1 \= UsedArgs0  % If these are equal, then we are at 
					% a fixed point, so further
					% analysis will not get any better
					% results.
	->
		% We can use the new Used Args values, and try again.
		call_termination_3(SCC, Module, Result, UsedArgs1, 
			Relation0, Relation)

	;
		Relation = Relation1,
		Result = Res1
	).

% This initialises the used arguments to be the set of input variables.
:- pred init_used_args(list(pred_proc_id), module_info, 
	map(pred_proc_id, set(var))).
:- mode init_used_args(in, in, out) is det.
init_used_args([], _, InitMap) :-
	map__init(InitMap).
init_used_args([PPId | PPIds], Module, UsedArgs) :-
	init_used_args(PPIds, Module, UsedArgs0),
	PPId = proc(PredId, ProcId),
	module_info_pred_proc_info(Module, PredId, ProcId, _, ProcInfo),
	proc_info_headvars(ProcInfo, Args),
	proc_info_argmodes(ProcInfo, ArgModes),
	partition_call_args(Module, ArgModes, Args, InArgs, _OutVars),
	set__list_to_set(InArgs, ArgSet),
	map__det_insert(UsedArgs0, PPId, ArgSet, UsedArgs).

:- pred termination_3_calc_unused_args(list(var), list(termination_3), 
	list(var)).
:- mode termination_3_calc_unused_args(in, in, out) is det.
termination_3_calc_unused_args(Vars, [], Vars).
termination_3_calc_unused_args(Vars0, [X | Xs], Vars) :-
	X = tuple(_, _, VarBag, _, _),
	termination_3_calc_unused_args_2(Vars0, VarBag, Vars1),
	termination_3_calc_unused_args(Vars1, Xs, Vars).

:- pred termination_3_calc_unused_args_2(list(var), bag(var), list(var)).
:- mode termination_3_calc_unused_args_2(in, in, out) is det.
termination_3_calc_unused_args_2([], _, []).
termination_3_calc_unused_args_2([ X | Xs ], Vars, Ys) :-
	( bag__contains(Vars, X) ->
		% If the variable is in the bag, then it is used.
		% Therefore, it should not be in the list of unused vars
		termination_3_calc_unused_args_2(Xs, Vars, Ys)
	;
		termination_3_calc_unused_args_2(Xs, Vars, Ys0),
		Ys = [X | Ys0]
	).

:- pred termination_3(list(pred_proc_id), module_info, 
	term_util__result(term_errors__error), map(pred_proc_id, set(var)),
	map(pred_proc_id, set(var)), relation(pred_proc_id),
	relation(pred_proc_id)).
:- mode termination_3(in, in, out, in, out, in, out) is det.
termination_3([], _Module, ok, UsedArgs, UsedArgs, Relation, Relation).
termination_3([ PPId | PPIds ], Module, Result, UsedArgs0, UsedArgs, 
		Relation0, Relation) :-
	% get goal info
	PPId = proc(PredId, ProcId),
	module_info_pred_proc_info(Module, PredId, ProcId, _PredInfo, ProcInfo),
	proc_info_termination(ProcInfo, Termination),
	( Termination = term(_Const, dont_know, _, MaybeError) ->
		% If the termination property is set to dont_know then
		% MaybeError should contain an error.  
		( MaybeError = yes(Error) ->
			Result = error(Error)
		;
			error("term_pass2.m: Unexpected value in term_pass2:termination_3")
		),
		UsedArgs = UsedArgs0,
		Relation = Relation0
	;
		proc_info_goal(ProcInfo, Goal),
		Goal = GoalExpr - GoalInfo,
		% Analyse goal info. This returns a list of ppid - size
		% pairs
		termination_3_goal(GoalExpr, GoalInfo, Module, total,
			call_info(PPId, UsedArgs0, no), Res0, [], Out),
		
		proc_info_argmodes(ProcInfo, ArgModes),
		proc_info_headvars(ProcInfo, Args),
		partition_call_args(Module, ArgModes, Args, InVars, _OutVars),
		bag__from_list(InVars, InVarsBag),
	
		( Res0 = ok ->
			termination_3_calc_unused_args(Args, Out, UnUsedArgs),
			map__lookup(UsedArgs0, PPId, OldUsedArgs),
			set__delete_list(OldUsedArgs, UnUsedArgs, NewUsedArgs),
			termination_3_add_arcs_to_relation(PPId, Out, 
				InVarsBag, Res1, Relation0, Relation1),
			( Res1 = ok ->
				termination_3(PPIds, Module, Result, 
					UsedArgs0, UsedArgs1, Relation1, 
					Relation)
			;
				% We failed because of positive value, or
				% because of not_subset.  Keep analysing,
				% to discover the used variables, of the other
				% procedures.
				termination_3(PPIds, Module, Res2, 
					UsedArgs0, UsedArgs1, Relation0, 
					_Relation),
				Relation = Relation0,
				% We know that Res1 is not_subset or
				% positive_value.  If Res2 is ok, then we
				% need to return Res1 (so that the calling
				% predicate knows that the analysis
				% failed). If Res2 is an error, then it
				% needs to be returned.  If Res2 is also
				% not_subset or positive_value, then fine,
				% the analysis will be re-run.  If it is
				% some other error, then re-running the
				% analysis will not gain anything.
				( Res2 = ok ->
					Result = Res1
				;
					Result = Res2
				)
			),
			% Add the used vars from the current pass to the
			% UsedArgs map.
			map__det_update(UsedArgs1, PPId, NewUsedArgs, UsedArgs)
		;
			UsedArgs = UsedArgs0,
			Result = Res0,
			Relation = Relation0
		)
	).

% This runs single argument analysis on the goal.  This is only run if
% normal termination analysis failed.  
:- pred termination_3_single_args(list(pred_proc_id), term_errors__error,
	map(pred_proc_id, set(var)), module_info, module_info, 
	io__state, io__state).
:- mode termination_3_single_args(in, in, in, in, out, di, uo) is det.
termination_3_single_args([], _, _, Module, Module) -->
	{ error("termination.m: there should be at least 1 predicate in a SCC\n") }.
termination_3_single_args([PPId | Rest], Error, UsedArgs, Module0, Module) -->
	globals__io_lookup_bool_option(termination_single_args, SingleArgs),
	{ SCC = [PPId | Rest] },
	{ PPId = proc(PredId, ProcId) },
	{ set__init(InitSet) },
	(
		{ SingleArgs = yes },
		{ Rest = [] },
		{ Error \= _ - imported_pred }
		% What other errors would prevent single argument analysis
		% from succeeding?
	->
		% can do single args
		{  module_info_pred_proc_info(Module0, PredId, ProcId, 
			_PredInfo, ProcInfo) },
		{ proc_info_goal(ProcInfo, Goal) },
		{ Goal = GoalExpr - GoalInfo },
		{ termination_3_goal(GoalExpr, GoalInfo, Module0,
			total, call_info(PPId, UsedArgs, yes), Res0,[],Out) },
		( { Res0 = error(Error2) } ->
			% The context of single_arg_failed needs to be the
			% same as the context of the Normal analysis error
			% message.
			{ Error = Context - _ },
			{ Error3 = Context - single_arg_failed(Error, Error2) },
			do_ppid_check_terminates(SCC, Error3, 
				Module0, Module)
			
		; { termination_3_single_2(Out, InitSet, InitSet) } ->
			% yeah, single arg succeded
			{ set_pred_proc_ids_terminates(SCC, yes, yes(Error),
				Module0, Module) }
		;
			% single argument analysis failed to prove
			% termination.  
			{ Error = Context - _ },
			{ Error2 = Context - single_arg_failed(Error) },
			do_ppid_check_terminates(SCC, Error2,
				Module0, Module)
		)
	;
		% cant do single args
		do_ppid_check_terminates(SCC, Error, 
			Module0, Module)
	).
		
:- pred termination_3_single_2(list(termination_3), set(var), set(var)).
:- mode termination_3_single_2(in, in, in) is semidet.
termination_3_single_2([], NegSet, NonNegSet) :-
	set__difference(NegSet, NonNegSet, DiffSet),
	% check that there is at least 1 headvar that is always strictly
	% decreasing
	set__remove_least(DiffSet, _, _).

termination_3_single_2([Off | Offs], NegSet0, NonNegSet0) :-
	Off = tuple(_, Int, VarBag0, MaybeVar, _Context),
	( 	
		MaybeVar = no,
		error("termination.m: Maybevar should be yes in single argument analysis\n")
	; 
		MaybeVar = yes(HeadVar),
		( 
			Int < 0,
			% Check that the variable that was recursed on did
			% not change positions between the head and
			% recursive call.  I am not sure if the first call
			% to bag__remove is actually required to succeed
			bag__remove(VarBag0, HeadVar, VarBag1),
			\+ bag__remove_smallest(VarBag1, _, _)
		->
			set__insert(NegSet0, HeadVar, NegSet),
			termination_3_single_2(Offs, NegSet, NonNegSet0)
		;
			set__insert(NonNegSet0, HeadVar, NonNegSet),
			termination_3_single_2(Offs, NegSet0, NonNegSet)
		)
	).

% This adds the information from termination_3_goal to the relation.
% the relation is between the procedures in the current SCC, with an arc
% showing that one procedure calls another with the size of the variables
% unchanged between the head and the (possibly indirect) recursive call.
% Any loops in the relation show possible non-termination. This predicate
% also checks that the calculated input variables are subsets of the actual
% input variables
:- pred termination_3_add_arcs_to_relation(pred_proc_id, list(termination_3), 
	bag(var), term_util__result(term_errors__error), 
	relation(pred_proc_id), relation(pred_proc_id)).
:- mode termination_3_add_arcs_to_relation(in, in, in, out, in, out) is det.
termination_3_add_arcs_to_relation(_PPid, [], _Vars, ok, Relation, Relation).
termination_3_add_arcs_to_relation(PPId, [X | Xs], Vars, Result, Relation0, 
		Relation) :-
	X = tuple(CalledPPId, Value, Bag, _Var, Context),
	( bag__is_subbag(Bag, Vars) ->
		compare(Res, Value, 0),
		( 
			Res = (>),
			Result = error(Context - 
				positive_value(PPId, CalledPPId)),
			Relation = Relation0
		;
			Res = (=),
			% Add the arc to the relation.
			relation__lookup_element(Relation0, PPId, Key),
			relation__lookup_element(Relation0, CalledPPId, 
				CalledKey),
			relation__add(Relation0, Key, CalledKey, Relation1),
			termination_3_add_arcs_to_relation(PPId, Xs, Vars, 
				Result, Relation1, Relation)
		;
			Res = (<),
			termination_3_add_arcs_to_relation(PPId, Xs, Vars, 
				Result, Relation0, Relation)
		)
	;
		Result = error(Context - not_subset(PPId, Bag, Vars)),
		Relation = Relation0
	).

:- pred add_pred_procs_to_relation(list(pred_proc_id), relation(pred_proc_id),
	relation(pred_proc_id)).
:- mode add_pred_procs_to_relation(in, in, out) is det.
add_pred_procs_to_relation([], Relation, Relation).
add_pred_procs_to_relation([PPId | PPIds], Relation0, Relation) :-
	relation__add_element(Relation0, PPId, _, Relation1),
	add_pred_procs_to_relation(PPIds, Relation1, Relation).

%-----------------------------------------------------------------------------%
% The relation that is passed in is a relation containing all of the procs
% in the current SCC.  It is used to check whether a call is recursive or not.
% termination_3_goal is the main section of the analysis for pass 2.  It
% processes the goal of a single procedure, and returns a list of
% termination_3 structures.  Each termination 3 structure represents a
% single (mutually or directly) recursive call, and also tracks the
% relative size of the input variables in the recursive call, in comparison
% to the head.
:- type call_info --->
	call_info(
		pred_proc_id,
		map(pred_proc_id, set(var)),
		bool % are we doing single arg.
	).


:- pred termination_3_goal(hlds_goal_expr, hlds_goal_info, module_info, 
	unify_info, call_info, term_util__result(term_errors__error), 
	list(termination_3), list(termination_3)).
:- mode termination_3_goal(in, in, in, in, in, out, in, out) is det.

termination_3_goal(conj(Goals), 
	_GoalInfo, Module, UnifyInfo, CallInfo, Res, Out0, Out) :-

	termination_3_goal_conj(Goals, Module, UnifyInfo, CallInfo, Res, 
		Out0, Out).

% termination_3_goal(call switches on the call_info argument as well.
termination_3_goal(call(CallPredId, CallProcId, Args, _IsBuiltin, _, _), 
		GoalInfo, Module, _UnifyInfo, call_info(PPId, UsedArgsMap, no), 
		Res, Out0, Out) :-
	PPId = proc(PredId, ProcId),
	CallPPId = proc(CallPredId, CallProcId),

	module_info_pred_proc_info(Module, PredId, ProcId, _, ProcInfo),
	module_info_pred_proc_info(Module, CallPredId, CallProcId, _,
		CallProcInfo),

	proc_info_vartypes(ProcInfo, VarType),
	proc_info_argmodes(CallProcInfo, CallArgModes),
	proc_info_termination(CallProcInfo, CallTermination),
	CallTermination = term(CallTermConst, CallTerminates, CallUsedArgs, _),
	goal_info_get_context(GoalInfo, Context),

	partition_call_args(Module, CallArgModes, Args, InVars, OutVars),
	bag__from_list(InVars, InVarBag0),
	bag__from_list(OutVars, OutVarBag),

	( CallUsedArgs = yes(UsedVars) ->
		remove_unused_args(InVarBag0, Args, UsedVars,
			InVarBag1)
	;
		InVarBag1 = InVarBag0
	),

	% step 1 - modify Out0
	( 
		CallTermConst = set(Int),
		termination_3_modify_out(InVarBag1, OutVarBag, Int,
			Out0, Out1),
		Res0 = ok
	;
		CallTermConst = not_set,
		error("Unexpected Termination Constant in termination.m"),
		Res0 = ok,
		Out1 = Out0
	;
		CallTermConst = inf(_),
		( termination_3_check_intersect(Out0, OutVarBag) ->
			% there is no intersection, so just continue
			Res0 = ok
		;
			Res0 = error(Context - 
				inf_termination_const(PPId, CallPPId))
		),
		Out1 = Out0
	),

	% step 2 - do we add another arc?
	( CallTerminates = dont_know ->
		Res = error(Context - dont_know_proc_called(PPId, CallPPId)),
		Out = Out0
	; \+ check_horder_args(Args, VarType) ->
		Res = error(Context - horder_args(PPId, CallPPId)),
		Out = Out0
	;
		( map__search(UsedArgsMap, CallPPId, RecursiveUsedArgs) ->
			% the called proc is in the map, so call is
			% recursive - add it to Out
			proc_info_headvars(CallProcInfo, HeadVars),
			termination_3_goal_call_2(Args, HeadVars, 
				RecursiveUsedArgs, Bag),
			NewOutElem = tuple(CallPPId, 0, Bag, no, Context),
			Out = [ NewOutElem | Out1 ]
		;
			% The call is not recursive
			Out = Out1
		),
		Res = Res0
	).
	
termination_3_goal(call(CallPredId, CallProcId, Args, _IsBuiltin, _, _), 
		GoalInfo, Module, _UnifyInfo, call_info(PPId, _Relation, yes), 
		Res, Out0, Out) :-
	PPId = proc(PredId, ProcId),
	CallPPId = proc(CallPredId, CallProcId),
	% could(should) do a sanity check to check that PPId is the only
	% PPId in Relation, but i dont see a reasonable way to do it.

	module_info_pred_proc_info(Module, PredId, ProcId, _, ProcInfo),
	module_info_pred_proc_info(Module, CallPredId, CallProcId, _,
		CallProcInfo),

	proc_info_vartypes(ProcInfo, VarType),
	proc_info_argmodes(CallProcInfo, CallArgModes),
	proc_info_headvars(CallProcInfo, HeadVars),
	proc_info_termination(CallProcInfo, CallTermination),
	CallTermination = term(_, CallTerminates, _CallUsedArgs, _),
	goal_info_get_context(GoalInfo, Context),

	partition_call_args(Module, CallArgModes, Args, InVars, OutVars),
	partition_call_args(Module, CallArgModes, HeadVars, InHeadVars, _),
	bag__from_list(OutVars, OutVarBag),

	% step 1 - modify Out0
	( termination_3_check_intersect(Out0, OutVarBag) ->
		% there is no intersection, so just continue
		Res0 = ok,
		Out1 = Out0
	;
		% This analysis could be much better, but it will do for
		% now.
		Res0 = error(Context - call_in_single_arg(CallPPId)),
		Out1 = Out0
	),

	% step 2 - do we add another arc?
	( CallTerminates = dont_know ->
		Res = error(Context - dont_know_proc_called(PPId, CallPPId)),
		Out = Out0
	; \+ check_horder_args(Args, VarType) ->
		Res = error(Context - horder_args(PPId, CallPPId)),
		Out = Out0
	;
		( CallPPId = PPId ->
			% call is recursive - add it to Out
			termination_3_goal_call(InVars, InHeadVars, PPId, 
				Context, Out1, Out)
		;
			% The call is not recursive
			Out = Out1
		),
		Res = Res0
	).
	
	
	

termination_3_goal(higher_order_call(_, _, _, _, _), 
	GoalInfo, _Module, _UnifyInfo, _CallInfo, Res, Out0, Out) :-

	goal_info_get_context(GoalInfo, Context),
	Res = error(Context - horder_call),
	Out = Out0.

termination_3_goal(switch(_Var, _CanFail, Cases, _StoreMap),
	_GoalInfo, Module, UnifyInfo, CallInfo, Res, Out0, Out) :-
	
	termination_3_goal_switch(Cases, Module, UnifyInfo, CallInfo, 
		Res, Out0, Out).

termination_3_goal(unify(_Var, _RHS, _UniMode, Unification, _Context),
	_GoalInfo, Module, FunctorAlg, _CallInfo, ok, Out0, Out) :-

	(
		Unification = construct(OutVar, ConsId, Args, Modes),
		split_unification_vars(Args, Modes, Module, InVarBag, 
			OutVarBag0),
		bag__insert(OutVarBag0, OutVar, OutVarBag),
		functor_norm(FunctorAlg, ConsId, Module, FunctorNorm),
		termination_3_modify_out(InVarBag, OutVarBag, 
			FunctorNorm, Out0, Out)
	;
		Unification = deconstruct(InVar, ConsId, Args, Modes, _),
		split_unification_vars(Args, Modes, Module, InVarBag0,
			OutVarBag),
		bag__insert(InVarBag0, InVar, InVarBag),
		functor_norm(FunctorAlg, ConsId, Module, FunctorNorm),
		termination_3_modify_out(InVarBag, OutVarBag, 
			(- FunctorNorm), Out0, Out)
	;
		Unification = assign(OutVar, InVar),
		bag__init(InitBag),
		bag__insert(InitBag, InVar, InVarBag),
		bag__insert(InitBag, OutVar, OutVarBag),
		termination_3_modify_out(InVarBag, OutVarBag, 0, Out0, Out)
	;
		Unification = simple_test(_InVar1, _InVar2),
		Out = Out0
	;
		Unification = complicated_unify(_, _),
		error("Unexpected complicated_unify in termination.m")
	).

termination_3_goal(disj(Goals, _StoreMap),
		_GoalInfo, Module, UnifyInfo, CallInfo, Res, Out0, Out) :-
	
	termination_3_goal_disj(Goals, Module, UnifyInfo, CallInfo, Res, 
		Out0, Out).

termination_3_goal(not(GoalExpr - GoalInfo),
	_GoalInfo, Module, UnifyInfo, CallInfo, Res, Out0, Out) :-
	
	termination_3_goal(GoalExpr, GoalInfo, Module, UnifyInfo, CallInfo, 
		Res, Out0, Out).

termination_3_goal(some(_Vars, GoalExpr - GoalInfo),
	_GoalInfo, Module, UnifyInfo, CallInfo, Res, Out0, Out) :-
	
	termination_3_goal(GoalExpr, GoalInfo, Module, UnifyInfo, CallInfo, 
		Res, Out0, Out).

termination_3_goal(if_then_else(_Vars, CondGoal, ThenGoal, ElseGoal, _),
	_GoalInfo, Module, UnifyInfo, CallInfo, Res, Out0, Out) :-
	
	CondGoal = CondExpr - CondGoalInfo,
	ThenGoal = ThenExpr - ThenGoalInfo,
	ElseGoal = ElseExpr - ElseGoalInfo,
	termination_3_goal(ThenExpr, ThenGoalInfo, Module, UnifyInfo, CallInfo, 
		ThenRes, Out0, ThenOut),
	termination_3_goal(ElseExpr, ElseGoalInfo, Module, UnifyInfo, CallInfo, 
		ElseRes, Out0, ElseOut),
	
	( ThenRes = error(_) ->
		Res = ThenRes,
		Out = ThenOut
	; ElseRes = error(_) ->
		Res = ElseRes,
		Out = ElseOut
	;
		% yeah, they both worked - join the outs
		list__append(ThenOut, ElseOut, Out1),
		termination_3_goal(CondExpr, CondGoalInfo, Module, 
			UnifyInfo, CallInfo, Res, Out1, Out)
	).
	
termination_3_goal(pragma_c_code(_, _, CallPredId, CallProcId, Args, _, _, _),
	GoalInfo, Module, _UnifyInfo, _CallInfo, Res, Out, Out) :-

	module_info_pred_proc_info(Module, CallPredId, CallProcId, _,
		CallProcInfo),
	proc_info_argmodes(CallProcInfo, CallArgModes),
	partition_call_args(Module, CallArgModes, Args, _InVars, OutVars),
	bag__from_list(OutVars, OutVarBag),

	( termination_3_check_intersect(Out, OutVarBag) ->
		% c_code has no important output variables, so we need no error
		Res = ok
	;
		goal_info_get_context(GoalInfo, Context),
		Res = error(Context - pragma_c_code)
	).

%-----------------------------------------------------------------------------%
% These following predicates all support termination_3_goal. 

:- pred termination_3_goal_conj(list(hlds_goal), module_info, 
	unify_info, call_info, term_util__result(term_errors__error), 
	list(termination_3), list(termination_3)).
:- mode termination_3_goal_conj(in, in, in, in, out, in, out) is det.
termination_3_goal_conj([] , _Module, _UnifyInfo, _CallInfo, ok, Out, Out).
termination_3_goal_conj([ Goal | Goals ], Module, UnifyInfo, CallInfo, 
		Res, Out0, Out) :-
	Goal = GoalExpr - GoalInfo,

	termination_3_goal_conj(Goals, Module, UnifyInfo, CallInfo, 
		Res0, Out0, Out1),
	( Res0 = ok ->
		termination_3_goal(GoalExpr, GoalInfo, Module, 
			UnifyInfo, CallInfo, Res, Out1, Out)
	;
		Res = Res0,
		Out = Out1
	).

% Used by single argument analysis to make a seperate Out for each input
% variable in a recursive call.
:- pred termination_3_goal_call(list(var), list(var), pred_proc_id, 
	term__context, list(termination_3), list(termination_3)).
:- mode termination_3_goal_call(in, in, in, in, in, out) is det.
termination_3_goal_call([], [], _, _, Out, Out).
termination_3_goal_call([_|_], [], _, _, Out, Out) :-
	error("term_pass2__termination_3_goal_call: Unmatched variables\n").
termination_3_goal_call([], [_|_], _, _, Out, Out) :-
	error("term_pass2:termination_3_goal_call: Unmatched variables\n").
termination_3_goal_call([ Var | Vars ], [ HeadVar | HeadVars ], PPId, 
		Context, Outs0, Outs) :-
	bag__init(Bag0),
	bag__insert(Bag0, Var, Bag),
	Out = tuple(PPId, 0, Bag, yes(HeadVar), Context),
	termination_3_goal_call(Vars, HeadVars, PPId, Context, 
		[Out | Outs0], Outs).

% Used to set the bag of input variables for a recursive call, according to
% the set of used arguments.
:- pred termination_3_goal_call_2(list(var), list(var), set(var), bag(var)).
:- mode termination_3_goal_call_2(in, in, in, out) is det.
termination_3_goal_call_2([], [], _, Out) :-
	bag__init(Out).
termination_3_goal_call_2([_|_], [], _, _Out) :-
	error("Unmatched vars in termination_3_goal_call_2\n").
termination_3_goal_call_2([], [_|_], _, _Out) :-
	error("Unmatched vars in termination_3_goal_call_2\n").
termination_3_goal_call_2([Var | Vars], [HeadVar | HeadVars], 
		UsedSet, OutBag) :-
	termination_3_goal_call_2(Vars, HeadVars, UsedSet, OutBag0),
	( set__member(HeadVar, UsedSet) ->
		bag__insert(OutBag0, Var, OutBag)
	;
		OutBag = OutBag0
	).


:- pred termination_3_goal_switch(list(case), module_info, 
	unify_info, call_info, term_util__result(term_errors__error), 
	list(termination_3), list(termination_3)).
:- mode termination_3_goal_switch(in, in, in, in, out, in, out) is det.
termination_3_goal_switch([] , _Module, _UnifyInfo, _CallInfo, ok, Out, Out) :-
    error("term_pass2:termination_3_goal_switch: unexpected empty switch\n").
termination_3_goal_switch([ Case | Cases ], Module, UnifyInfo, 
		CallInfo, Res, Out0, Out):-
	Case = case(_, Goal),
	Goal = GoalExpr - GoalInfo,

	( Cases = [] ->
		Res1 = ok,
		Out1 = Out0
	;
		termination_3_goal_switch(Cases, Module, UnifyInfo, CallInfo, 
			Res1, Out0, Out1)
	),
	( Res1 = ok ->
		termination_3_goal(GoalExpr, GoalInfo, 
			Module, UnifyInfo, CallInfo, Res, Out0, Out2),
		list__append(Out1, Out2, Out)
	;
		Res = Res1,
		Out = Out1
	).

:- pred termination_3_goal_disj(list(hlds_goal), module_info, 
	unify_info, call_info, term_util__result(term_errors__error), 
	list(termination_3), list(termination_3)).
:- mode termination_3_goal_disj(in, in, in, in, out, in, out) is det.
termination_3_goal_disj([] , _Module, _UnifyInfo, _CallInfo, ok, Out, Out):-
	( Out = [] ->
		true
	;
		error("term_pass2:termination_3_goal_disj: Unexpected value after disjunction\n")
	).
termination_3_goal_disj([ Goal | Goals ], Module, UnifyInfo, 
		CallInfo, Res, Out0, Out) :-
	Goal = GoalExpr - GoalInfo,

	( Goals = [] ->
		Res1 = ok, 
		Out1 = Out0
	;
		termination_3_goal_disj(Goals, Module, UnifyInfo, CallInfo, 
			Res1, Out0, Out1)
	),
	( Res1 = ok ->
		termination_3_goal(GoalExpr, GoalInfo, Module, 
			UnifyInfo, CallInfo, Res, Out0, Out2),
		list__append(Out1, Out2, Out)
	;
		Res = Res1,
		Out = Out1
	).


:- pred termination_3_check_intersect(list(termination_3), bag(var)).
:- mode termination_3_check_intersect(in, in) is semidet.

% termination_3_check_intersect succeeds if there is no intersection
% between any one of the Outs and the OutVarBag.
termination_3_check_intersect([ ], _).
termination_3_check_intersect([ Out | Outs ], OutVarBag) :-
	Out = tuple(_PPId, _Const, OutBag, _Var, _Context),
	\+ bag__intersect(OutBag, OutVarBag),
	termination_3_check_intersect(Outs, OutVarBag).

:- pred termination_3_modify_out(bag(var), bag(var), int, list(termination_3), 
	list(termination_3)).
:- mode termination_3_modify_out(in, in, in, in, out) is det.
termination_3_modify_out(_, _, _, [], []).
termination_3_modify_out(InVars, OutVars, Off, [Out0 | Out0s], [Out | Outs]):-
	Out0 = tuple(PPId, Int0, Vars0, Var, Context),
	( bag__intersect(OutVars, Vars0) ->
		% There is an intersection.
		bag__subtract(Vars0, OutVars, Vars1),
		bag__union(InVars, Vars1, Vars),
		Int = Int0 + Off,
		Out = tuple(PPId, Int, Vars, Var, Context)
	;
		% There is not an intersection.
		Out = Out0
	),
	termination_3_modify_out(InVars, OutVars, Off, Out0s, Outs).
