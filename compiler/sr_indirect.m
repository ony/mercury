%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_indirect
% Main authors: nancy
% 
% Determine the indirect reuse.  This requires a fixpoint computation.
%
%-----------------------------------------------------------------------------%

:- module sr_indirect.
:- interface.

% library modules.
:- import_module io. 

% XXX parent modules. 
:- import_module hlds.
% compiler modules. 
:- import_module hlds__hlds_module.

:- pred sr_indirect__compute_fixpoint(module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

% XXX parent modules. 
:- import_module transform_hlds, parse_tree, libs.

:- import_module map, list, std_util, require, set, string, bool.
:- import_module hlds__hlds_pred, hlds__hlds_goal, hlds__passes_aux.
:- import_module transform_hlds__dependency_graph.
:- import_module parse_tree__prog_data, parse_tree__prog_util.
:- import_module pa_alias_as, pa_run.
:- import_module pa_sr_util.
:- import_module sr_data, sr_util, sr_live.
:- import_module sr_fixpoint_table.
:- import_module libs__globals, libs__options.
:- import_module pa_datastruct. 

compute_fixpoint(HLDS0, HLDSout) -->
		% compute the strongly connected components
	{ module_info_ensure_dependency_info(HLDS0, HLDS1) },
	{ module_info_get_maybe_dependency_info(HLDS1, MaybeDepInfo) } ,
	(
		{ MaybeDepInfo = yes(DepInfo) }
	->
		{ hlds_dependency_info_get_dependency_ordering(DepInfo,
				DepOrdering) },
		% perform the analysis, and annotate the procedures
		run_with_dependencies(DepOrdering, HLDS1, HLDS2),
		{ HLDSout = HLDS2 }
	;
		{ error("(sr_indirect) compute_fixpoint: no dependency info") }
	).

:- pred run_with_dependencies(dependency_ordering, module_info, 
					module_info, io__state, io__state).
:- mode run_with_dependencies(in, in, out, di, uo) is det.

run_with_dependencies(Deps, HLDSin, HLDSout) -->
	list__foldl2(run_with_dependency, Deps, HLDSin, HLDSout).

:- pred run_with_dependency(list(pred_proc_id), module_info, module_info,
				io__state, io__state).
:- mode run_with_dependency(in, in, out, di, uo) is det.

run_with_dependency(SCC, HLDSin, HLDSout) -->
	(
		% analysis ignores special predicates
		{ pa_sr_util__some_are_special_preds(SCC, HLDSin) }
	->
		{ HLDSout = HLDSin }
	;
		% for each list of strongly connected components, 
		% perform a fixpoint computation.
		{ sr_fixpoint_table_init(HLDSin, SCC, FPtable0) } , 
		run_with_dependency_until_fixpoint(SCC, FPtable0, 
					HLDSin, HLDSout)
	).

%-----------------------------------------------------------------------------%
:- pred run_with_dependency_until_fixpoint(list(pred_proc_id), 
		sr_fixpoint_table__table, module_info, module_info,
		io__state, io__state).
:- mode run_with_dependency_until_fixpoint(in, in, in, out, di, uo) is det.

run_with_dependency_until_fixpoint(SCC, FPtable0, HLDSin, HLDSout) -->
	list__foldl2(analyse_pred_proc(HLDSin), SCC, FPtable0, FPtable),
	(
		{ sr_fixpoint_table_all_stable(FPtable) }
	->
		{ list__foldl(update_goal_in_module_info(FPtable), SCC,
				HLDSin, HLDSout) }
	;
		{ sr_fixpoint_table_new_run(FPtable, 
				FPtable1) },
		run_with_dependency_until_fixpoint(SCC, FPtable1, HLDSin, 
				HLDSout)
	).

:- pred update_goal_in_module_info(sr_fixpoint_table__table::in, 
		pred_proc_id::in, module_info::in, module_info::out) is det.

update_goal_in_module_info(FP, PredProcId, HLDS0, HLDS) :- 
	PredProcId = proc(PredId, ProcId), 
	sr_fixpoint_table_get_final_reuse(PredProcId, Memo, Goal, FP), 
	module_info_pred_proc_info(HLDS0, PredProcId, PredInfo0, ProcInfo0),
	proc_info_set_goal(ProcInfo0, Goal, ProcInfo1), 
	memo_reuse_simplify(Memo, MemoS),
	proc_info_set_reuse_information(ProcInfo1, MemoS, ProcInfo),
	pred_info_procedures(PredInfo0, Procedures0), 
	map__det_update(Procedures0, ProcId, ProcInfo, Procedures), 
	pred_info_set_procedures(PredInfo0, Procedures, PredInfo), 
	module_info_set_pred_info(HLDS0, PredId, PredInfo, HLDS).
	
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
:- pred analyse_pred_proc(module_info, pred_proc_id, 
				sr_fixpoint_table__table,
				sr_fixpoint_table__table, 
				io__state, io__state).
:- mode analyse_pred_proc(in, in, in, out, di, uo) is det.

analyse_pred_proc(HLDS, PredProcId, FPin, FPout) --> 
	{ module_info_pred_proc_info(HLDS, PredProcId,
		_PredInfo, ProcInfo) },
	{ PredProcId = proc(PredId, ProcId) },

	globals__io_lookup_bool_option(very_verbose, VeryVerbose), 
	(
		{ VeryVerbose = no }
	->
		[]
	;
		{ sr_fixpoint_table_which_run(FPin, Run) }, 
		{ string__int_to_string(Run, SRun) }, 
		{ string__append_list([ 
			"% Indirect reuse analysing (run ", SRun, ") "],
			Msg) },
		passes_aux__write_proc_progress_message(Msg, 
			PredId, ProcId, HLDS), 
		{ sr_fixpoint_table_get_final_reuse(PredProcId, M, _, FPin) }, 

		(
			{ M = yes(Conditions) }
		-> 
			{ list__length(Conditions, Length) }, 
			{ string__int_to_string(Length, LengthS) }, 
			{ string__append_list(
					["%\tNumber of conditions (before):\t",
					LengthS, "\n"], Msg2) } ,
			maybe_write_string(VeryVerbose, Msg2)
		; 
			maybe_write_string(VeryVerbose, "%\tNo reuse.\n")
		)
	),
	{ 
		% initialize all the necessary information to get the
		% analysis started.

		% 1. get ProcInfo
		%	OK
		% 2. get Goal
		proc_info_goal(ProcInfo, Goal0),
		%   	OK
		% 3. initialize alias-information
		pa_alias_as__init(Alias0),
		%	OK
		% 4. initialize reuses-information
		hlds_pred__proc_info_headvars(ProcInfo, HVs), 
		% do not change the state of the fixpoint table by
		% simply consulting it now for initialization.
		sr_fixpoint_table_get_final_reuse(PredProcId, 
				MemoStarting, _, FPin),
		indirect_reuse_pool_init(HVs, MemoStarting, Pool0), 
		% 5. analyse_goal
		analyse_goal(ProcInfo, HLDS, 
					Goal0, Goal,
					analysis_info(Alias0, Pool0,
							set__init, FPin),
					analysis_info(_Alias, Pool,
							_Static, FP1)),
		/*
		analyse_goal(ProcInfo, HLDS, 
					Goal0, Goal,
					Pool0, Pool,
					Alias0, _Alias, 
					FPin, FP1),
		*/
		% 	OK
		% 6. update all kind of information
		indirect_reuse_pool_get_memo_reuse(Pool, Memo), 
		sr_fixpoint_table_new_reuse(PredProcId,
				Memo, Goal, FP1, FPout)
	},
	(
		{ VeryVerbose = no }
	->
		[]
	;
		{ sr_fixpoint_table_get_final_reuse(PredProcId,M1,_,FPout) }, 

		(
			{ M1 = yes(Conditions1) }
		-> 
			{ list__length(Conditions1, Length1) }, 
			{ string__int_to_string(Length1, LengthS1) }, 
			{ string__append_list(
					["%\tNumber of conditions (after):\t",
					LengthS1, "\n"], Msg21) } ,
			maybe_write_string(VeryVerbose, Msg21)
		; 
			maybe_write_string(VeryVerbose, "%\tNo reuse.\n")
		)
	).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- type analysis_info
	--->	analysis_info(
			alias	:: alias_as,
			pool	:: indirect_reuse_pool,
			static	:: set(prog_var),
			table	:: sr_fixpoint_table__table
		).

:- pred analyse_goal(proc_info::in, module_info::in, 
			hlds_goal::in, hlds_goal::out,
			analysis_info::in, analysis_info::out) is det.

analyse_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = conj(Goals0), 
	list__map_foldl(analyse_goal(ProcInfo, HLDS), Goals0, Goals, AI0, AI),
	Expr = conj(Goals),
	Info = Info0,
	Goal = Expr - Info. 

analyse_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = call(PredId, ProcId, ActualVars, _, _, _), 
	proc_info_vartypes(ProcInfo, VarTypes),
	list__map(
		map__lookup(VarTypes), 
		ActualVars,
		ActualTypes), 
	call_verify_reuse(ProcInfo, HLDS,
			PredId, ProcId, ActualVars, 
			ActualTypes, Info0, Info, AI0, AI1, _),
	pa_run__extend_with_call_alias(HLDS, ProcInfo, 
		PredId, ProcId, ActualVars, ActualTypes, AI0 ^ alias, Alias),
	AI = AI1 ^ alias := Alias,
	Expr = Expr0, 
	Goal = Expr - Info.

analyse_goal(_ProcInfo, _HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = generic_call(_, _, _, _), 
	pa_alias_as__top("unhandled goal", Alias), 
	AI = AI0 ^ alias := Alias,
	Goal = Expr0 - Info0. 

analyse_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = unify(_Var, _Rhs, _Mode, Unification, _Context), 

		% Record the statically constructed variables.
	( Unification = construct(Var, _, _, _,
			construct_statically(_), _, _) ->
		AI1 = AI0 ^ static := set__insert(AI0 ^ static, Var)
	;
		AI1 = AI0
	),
	pa_alias_as__extend_unification(ProcInfo, HLDS, 
			Unification, Info, AI0 ^ alias, Alias),	
	AI = AI1 ^ alias := Alias,
	Info = Info0,
	Expr = Expr0, 
	Goal = Expr - Info. 

analyse_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = switch(Var, CanFail, Cases0),
	list__map_foldl(
		(pred(case(ConsId, Gin)::in, Tuple::out,
				FPin::in, FPout::out) is det :-
			analyse_goal(ProcInfo, HLDS, Gin, Gout, 
				analysis_info(AI0 ^ alias, AI0 ^ pool,
						AI0 ^ static, FPin),
				analysis_info(NewAlias,
						NewPool, NewStatic, FPout)),
			Tuple = { case(ConsId, Gout), NewAlias, NewPool,
					NewStatic }
		),
		Cases0, Tuples,
		AI0 ^ table, FP),

	Cases = list__map((func({C, _A, _P, _S}) = C), Tuples),
	ListPools = list__map((func({_G, _A, P, _S}) = P), Tuples),
	ListAliases = list__map((func({_G, A, _P, _S}) = A), Tuples),
	ListStatic = list__map((func({_G, _A, _P, S}) = S), Tuples),

	indirect_reuse_pool_least_upper_bound_disjunction(
				ListPools,
				Pool),
	pa_alias_as__least_upper_bound_list(ProcInfo, HLDS, Info0, 
				ListAliases,
				Alias1),
	set__power_union(set__list_to_set(ListStatic), Static),

	% reduce the aliases
	project_on_live_vars(ProcInfo, Info0, Alias1, Alias),

	AI = analysis_info(Alias, Pool, Static, FP),

	Info = Info0,
	Expr = switch(Var, CanFail, Cases),
	Goal = Expr - Info. 

analyse_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = disj(Goals0),
	(
		Goals0 = []
	->
		Goals = Goals0,
		AI0 = AI
	;
		% XXX up to here
		list__map_foldl(
			(pred(Gin::in, Tuple::out,
					FPin::in, FPout::out) is det :-
				analyse_goal(ProcInfo, HLDS, Gin, Gout, 
					analysis_info(AI0 ^ alias, AI0 ^ pool,
							AI0 ^ static, FPin),
					analysis_info(NewAlias, NewPool,
							NewStatic, FPout)),
				Tuple = { Gout, NewAlias, NewPool, NewStatic }
			),
			Goals0, Tuples,
			AI0 ^ table, FP),

		Goals = list__map((func({G, _A, _P, _S}) = G), Tuples),
		ListPools = list__map((func({_G, _A, P, _S}) = P), Tuples),
		ListAliases = list__map((func({_G, A, _P, _S}) = A), Tuples),
		ListStatic = list__map((func({_G, _A, _P, S}) = S), Tuples),
		set__power_union(set__list_to_set(ListStatic), Static),

		indirect_reuse_pool_least_upper_bound_disjunction(
					ListPools,
					Pool),
		pa_alias_as__least_upper_bound_list(ProcInfo, HLDS, Info0, 
					ListAliases,
					Alias1),

		% reduce the aliases
		pa_alias_as__project_on_live_vars(ProcInfo, Info, Alias1, 
					Alias),

		AI = analysis_info(Alias, Pool, Static, FP)
	),

	Info = Info0,
	Expr = disj(Goals),
	Goal = Expr - Info. 

analyse_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = not(NegatedGoal0),
	analyse_goal(ProcInfo, HLDS, NegatedGoal0, NegatedGoal, AI0, AI),
	Info = Info0, 
	Expr = not(NegatedGoal),
	Goal = Expr - Info. 

analyse_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = some(A, B, SomeGoal0), 
	analyse_goal(ProcInfo, HLDS, SomeGoal0, SomeGoal, AI0, AI),
	Info = Info0, 
	Expr = some(A, B, SomeGoal), 
	Goal = Expr - Info.

analyse_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = if_then_else(Vars, Cond0, Then0, Else0),
	analyse_goal(ProcInfo, HLDS, Cond0, Cond, AI0, AI_Cond),
	analyse_goal(ProcInfo, HLDS, Then0, Then, AI_Cond, AI_Then),

	AI1 = AI0 ^ table := AI_Then ^ table,
	analyse_goal(ProcInfo, HLDS, Else0, Else, AI1, AI_Else),

	indirect_reuse_pool_least_upper_bound_disjunction(
				[AI_Then ^ pool, AI_Else ^ pool],
				Pool),

	pa_alias_as__least_upper_bound_list(ProcInfo, HLDS, Info0, 
				[AI_Then ^ alias, AI_Else ^ alias],
				Alias1),
	Static = AI_Then ^ static `set__union` AI_Else ^ static,
	
	% reduce the aliases
	goal_info_get_outscope(Info, Outscope),
	pa_alias_as__project_set(Outscope, Alias1, Alias),

	AI = analysis_info(Alias, Pool, Static, AI1 ^ table),

	Info = Info0,
	Expr = if_then_else(Vars, Cond, Then, Else),
	Goal = Expr - Info.

analyse_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = foreign_proc(Attrs, PredId, ProcId, 
					Vars, MaybeModes, Types, _), 
	pa_alias_as__extend_foreign_code(HLDS, ProcInfo, Attrs, 
			PredId, ProcId, Vars, 
			MaybeModes, Types, Info0, AI0 ^ alias, Alias),
	AI = AI0 ^ alias := Alias,
	Goal = Expr0 - Info0. 

analyse_goal(_ProcInfo, _HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = par_conj(_), 
	pa_alias_as__top("unhandled goal (par_conj)", Alias), 
	AI = AI0 ^ alias := Alias,
	Goal = Expr0 - Info0. 

analyse_goal(_ProcInfo, _HLDS, Expr0 - Info0, Goal, AI0, AI) :-
	Expr0 = shorthand(_), 
	pa_alias_as__top("unhandled goal (shorthand)", Alias), 
	AI = AI0 ^ alias := Alias,
	Goal = Expr0 - Info0. 


:- pred call_verify_reuse(proc_info::in, module_info::in,
		pred_id::in, proc_id::in, list(prog_var)::in,
		list((type))::in, 
		hlds_goal_info::in, hlds_goal_info::out, 
		analysis_info::in, analysis_info::out, bool::out) is det.

call_verify_reuse(ProcInfo, ModuleInfo, PredId, ProcId, ActualVars,
		ActualTypes, 
		GoalInfo0, GoalInfo, analysis_info(Alias0, Pool0, Static, FP0),
		analysis_info(Alias0, Pool, Static, FP), YesNo) :-
	call_verify_reuse(ProcInfo, ModuleInfo, PredId, ProcId, ActualVars,
			ActualTypes, 
			Alias0, Static, Pool0, Pool, GoalInfo0, GoalInfo,
			FP0, FP, YesNo).

:- pred call_verify_reuse(proc_info::in, module_info::in, pred_id::in,
		proc_id::in, list(prog_var)::in, list((type))::in, 
		alias_as::in,
		set(prog_var)::in, indirect_reuse_pool::in,
		indirect_reuse_pool::out, hlds_goal_info::in ,
		hlds_goal_info::out, sr_fixpoint_table__table::in,
		sr_fixpoint_table__table::out, bool::out) is det.

call_verify_reuse(ProcInfo, HLDS, PredId0, ProcId0, 
			ActualVars, ActualTypes, Alias0, 
			StaticTerms, Pool0, Pool, 
			Info0, Info, FP0, FP, YesNo) :- 

	module_info_structure_reuse_info(HLDS, ReuseInfo),
	ReuseInfo = structure_reuse_info(ReuseMap),
	(map__search(ReuseMap, proc(PredId0, ProcId0), Result) ->
		Result = proc(PredId, ProcId) - _Name
	;
		PredId = PredId0,
		ProcId = ProcId0
	),

	% 0. fetch the procinfo of the called procedure:
	module_info_pred_proc_info(HLDS, PredId, ProcId, PredInfo, 
					ProcInfo0),
	% 1. find the tabled reuse for the called predicate
	lookup_memo_reuse(PredId, ProcId, HLDS, FP0, FP,
					FormalMemo),	
	% 2. once found, we can immediately handle the case where
	% the tabled reuse would say that reuse is not possible anyway:
	(
		% unconditional reuse
		FormalMemo = yes([])
	->
		indirect_reuse_pool_add_unconditional(Pool0, Pool), 
		Info = Info0, 
		YesNo = yes
	;
		% no reuse possible anyway
		(
			memo_reuse_top(FormalMemo) ; 
			pa_alias_as__is_top(Alias0)
		)
	->
		Pool = Pool0,
		Info = Info0, 
		YesNo = no
	;
		memo_reuse_rename(ProcInfo0, ActualVars, FormalMemo, 
					Memo0), 
		pred_info_arg_types(PredInfo, FormalTypes) ,
		memo_reuse_rename_types(FormalTypes, ActualTypes, 
					Memo0, Memo),
		% 3. compute the Live variables upon a procedure entry:
		% 3.a. compute the full live set at the program point of
		%      the call.
		sr_live__init(LIVE0),
			% usually this should be the output variables
			% of the procedure which we're analysing, yet
			% output variables are guaranteed to belong to 
			% the LFUi set, so there is no loss in taking
			% LIVE0 as the empty live-set.
		goal_info_get_lfu(Info0, LFUi),
		goal_info_get_lbu(Info0, LBUi),
		set__union(LFUi, LBUi, LUi),
		pa_alias_as__live(HLDS, ProcInfo, LUi, LIVE0, Alias0, Live_i),
		% 3.b. project the live-set to the actual vars:
		sr_live__project(ActualVars, Live_i, ActualLive_i),
		% 4. project the aliases to the actual vars
		pa_alias_as__project(ActualVars, Alias0, ActualAlias_i),
		(
				% XXX replace that with the actual
				% static set!
			memo_reuse_verify_reuse(ProcInfo, HLDS, 
				Memo, ActualLive_i, ActualAlias_i,
				StaticTerms)
		->
			indirect_reuse_pool_add(HLDS, ProcInfo,
				Memo, LFUi, LBUi, 
				Alias0, ConditionalReuse, Pool0, Pool),
			ReuseCall = reuse_call(ConditionalReuse),
			(
				ConditionalReuse = yes,
				KindReuse = potential_reuse(ReuseCall)
			;
				ConditionalReuse = no, 
				% If the reuse is unconditional, then
				% reuse is not just potentially possible, 
				% but alwasy possible, so skipping the
				% potential phase is perfectly safe. 
				% (see also
				% sr_choice_graphing__annotate_reuses)
				KindReuse = reuse(ReuseCall)
			),
			goal_info_set_reuse(Info0, KindReuse, Info),
			YesNo = yes
		;
			Pool = Pool0,
	
			examine_cause_of_missed_reuse(HLDS, ProcInfo, 
					LFUi, LBUi, 
					StaticTerms, Memo, 
					Cause), 
			
			goal_info_set_reuse(Info0, 
				potential_reuse(missed_reuse_call(Cause)), Info), 
			YesNo = no
		)
	).

:- pred examine_cause_of_missed_reuse(module_info::in, 
			proc_info::in, 
			set(prog_var)::in, 
			set(prog_var)::in, 
			set(prog_var)::in, 
			memo_reuse::in, list(string)::out) is det. 
examine_cause_of_missed_reuse(ModuleInfo, ProcInfo, 
		LFU, LBU, Static, Memo, Causes) :- 
	(
		Memo = yes(Conditions) 
	->
		list__filter_map(
			examine_cause_of_missed_condition(ModuleInfo,
						ProcInfo, 
						LFU, LBU, Static), 
			Conditions, 
			Causes)
	;
		Cause = "No failed reuse because there is no reuse.",
		Causes = [Cause]
	).

:- pred examine_cause_of_missed_condition(module_info::in, 
			proc_info::in, 
			set(prog_var)::in, 
			set(prog_var)::in, 
			set(prog_var)::in, 
			reuse_condition::in, 
			string::out) is semidet.

examine_cause_of_missed_condition(ModuleInfo, ProcInfo, 
		LFU, LBU, StaticVars, Condition, Cause) :- 
	sr_live__init(DummyLive), 
	pa_alias_as__init(BottomAlias), 
	pa_alias_as__live(ModuleInfo, ProcInfo, 
			LFU, DummyLive, BottomAlias, LFU_Live), 
	pa_alias_as__live(ModuleInfo, ProcInfo, 
			LBU, DummyLive, BottomAlias, LBU_Live), 
	Condition = condition(Nodes, _LU, _LA), 
	% 
	NodesL = set__to_sorted_list(Nodes),
	(
		% check whether reason for no reuse is StaticVars
		list__filter_map(
			(pred(Node::in, Var::out) is semidet :- 
				get_var(Node, Var),
				set__member(Var, StaticVars)
			), 
			NodesL, 
			R), 
		R \= []
	->
		% due to static vars
		Cause = "Node is static."
	;
		% not due to static vars
		% check for LFU
		list__filter(
			(pred(D::in) is semidet :- 
			  sr_live__is_live_datastruct(ModuleInfo, 
				ProcInfo, D, LFU_Live)
			), 
			NodesL, 
			RF), 
		RF \= []
	-> 
		% due to lfu
		Cause = "Node is in local forward use."
	;
		% not due to LFU
		% check LBU
		list__filter(
			(pred(D::in) is semidet :- 
			  sr_live__is_live_datastruct(ModuleInfo, 
				ProcInfo, D, LBU_Live)
			), 
			NodesL, 
			RB), 
		RB \= []
	->
		% due to lbu
		Cause = "Node is in local backward use."
	; 
		Cause = "Node is live because it has a live alias."
	).

				
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
:- pred lookup_memo_reuse(pred_id, proc_id, module_info, 
		sr_fixpoint_table__table, sr_fixpoint_table__table, 
		memo_reuse).
:- mode lookup_memo_reuse(in, in, in, in, out, out) is det.

	% similar to the lookup_call_alias from pa_run:
	% 1. check in fixpoint table
	% 2. check in module_info (already fully analysed or imported pred)
	%    no special treatment necessary for primitive predicates and
	%    alike, as the default of predicates is no reuse anyway.
lookup_memo_reuse(PredId, ProcId, HLDS, FP0, FP, Memo):- 
	PredProcId = proc(PredId, ProcId),
	(
		% 1 - check in table
		sr_fixpoint_table_get_reuse(PredProcId, 
					Memo1, FP0, FP1)
	->
		Memo = Memo1,
		FP = FP1
	;
		FP = FP0,
		% 2 - lookup in module_info
		module_info_pred_proc_info(HLDS, PredProcId, _PredInfo,
						ProcInfo),
		proc_info_reuse_information(ProcInfo, Memo)
	).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- type indirect_reuse_pool ---> 
		pool(
			list(prog_var), % real headvars
			memo_reuse
		).

:- pred indirect_reuse_pool_init(list(prog_var)::in, 
		memo_reuse::in, 
		indirect_reuse_pool::out) is det.
:- pred indirect_reuse_pool_get_memo_reuse(indirect_reuse_pool::in, 
		memo_reuse::out) is det.
:- pred indirect_reuse_pool_least_upper_bound_disjunction(
		list(indirect_reuse_pool)::in, 
		indirect_reuse_pool::out) is det.
:- pred indirect_reuse_pool_least_upper_bound(
		indirect_reuse_pool::in,
		indirect_reuse_pool::in, 
		indirect_reuse_pool::out) is det.
:- pred indirect_reuse_pool_add(module_info::in, proc_info::in, 
		memo_reuse::in, 
		set(prog_var)::in, set(prog_var)::in, alias_as::in, bool::out,
		indirect_reuse_pool::in, indirect_reuse_pool::out) is det. 
:- pred indirect_reuse_pool_add_unconditional(indirect_reuse_pool::in, 
		indirect_reuse_pool::out) is det.
		

indirect_reuse_pool_init(HVs, MEMO, pool(HVs, MEMO)).
indirect_reuse_pool_get_memo_reuse(pool(_, MEMO), MEMO). 

indirect_reuse_pool_least_upper_bound_disjunction(List, Pool):-
	(
		List = [ P1 | R ]
	->
		list__foldl(
			indirect_reuse_pool_least_upper_bound,
			R, 
			P1, 
			Pool)
	;
		require__error("(sr_indirect) indirect_reuse_pool_least_upper_bound_disjunction: list is empty")
	).

:- import_module hlds__instmap.

indirect_reuse_pool_least_upper_bound(Pool1, Pool2, Pool):-
	Pool1 = pool(HVS, Memo1), 
	Pool2 = pool(_, Memo2), 
	memo_reuse_merge(Memo1, Memo2, Memo), 
	Pool = pool(HVS, Memo). 

indirect_reuse_pool_add(HLDS, ProcInfo, MemoReuse, 	
		LFUi, LBUi, Alias0, ConditionalReuse, Pool0, Pool) :- 

	(
		MemoReuse = yes(OldConditions)
	->
			% XXX instmap here simply initialized, as currently
			% it's not used in the normalization anyway.. 	
		instmap__init_reachable(InstMap0), 
		pa_alias_as__normalize(ProcInfo, HLDS, InstMap0, 
				Alias0, Alias), 
		
		Pool0 = pool(HVS, ExistingMemo), 
		list__map(
			reuse_condition_update(ProcInfo, HLDS, 
				LFUi, LBUi, Alias, HVS), 
			OldConditions,
			NewConditions0),
		reuse_conditions_simplify(NewConditions0, NewConditions), 
			% Does this reuse introduce any new conditions
			% on the head variables.
		( NewConditions = [] ->
			ConditionalReuse = no
		;
			ConditionalReuse = yes
		),
		memo_reuse_merge(ExistingMemo, yes(NewConditions), 
				NewMemo), 
		Pool = pool(HVS, NewMemo)
	;
		error("indirect_reuse_pool_add: never enter.")
	).

indirect_reuse_pool_add_unconditional(Pool0, Pool) :- 
	Pool0 = pool(Hvs, Memo0),
	(
		Memo0 = no
	->
		Memo = yes([])
	;
		Memo = Memo0
	),
	Pool = pool(Hvs, Memo).



	


