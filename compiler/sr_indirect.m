%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
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

:- module structure_reuse__sr_indirect.
:- interface.

:- import_module hlds__hlds_module.
:- import_module possible_alias__pa_alias_as.
:- import_module structure_reuse__sr_data.

:- import_module io. 

:- pred sr_indirect__compute_fixpoint(alias_as_table::in, 
		reuse_condition_table::in, reuse_condition_table::out, 
		module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_pred.
:- import_module hlds__instmap.
:- import_module hlds__passes_aux.
:- import_module libs__globals.
:- import_module libs__options.
:- import_module parse_tree__prog_data.
:- import_module parse_tree__prog_util.
:- import_module possible_alias__pa_datastruct. 
:- import_module possible_alias__pa_alias_as.
:- import_module possible_alias__pa_run.
:- import_module possible_alias__pa_sr_util.
:- import_module structure_reuse__sr_fixpoint_table.
:- import_module structure_reuse__sr_live.
:- import_module transform_hlds__dependency_graph.

:- import_module map, list, std_util, require, set, string, bool.

compute_fixpoint(AliasTable, !ReuseTable, !ModuleInfo, !IO) :- 
		% compute the strongly connected components
	module_info_ensure_dependency_info(!ModuleInfo), 
	module_info_get_maybe_dependency_info(!.ModuleInfo, MaybeDepInfo),
	(
		MaybeDepInfo = yes(DepInfo)
	->
		hlds_dependency_info_get_dependency_ordering(DepInfo,
				DepOrdering),
		% perform the analysis, and annotate the procedures
		run_with_dependencies(AliasTable, DepOrdering, 
			!ReuseTable, !ModuleInfo, !IO)
	;
		error("(sr_indirect) compute_fixpoint: no dependency info")
	).

:- pred run_with_dependencies(alias_as_table::in, dependency_ordering::in, 
		reuse_condition_table::in, reuse_condition_table::out, 
		module_info::in, module_info::out, 
		io__state::di, io__state::uo) is det.

run_with_dependencies(AliasTable, Deps, !ReuseTable, !ModuleInfo, !IO) :- 
	list__foldl3(run_with_dependency(AliasTable), Deps, 
			!ReuseTable, !ModuleInfo, !IO). 

:- pred run_with_dependency(alias_as_table::in, list(pred_proc_id)::in, 
		reuse_condition_table::in, reuse_condition_table::out, 
		module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.

run_with_dependency(AliasTable, SCC, !ReuseTable, !ModuleInfo, !IO) :- 
	(
		% analysis ignores special predicates
		pa_sr_util__some_are_special_preds(SCC, !.ModuleInfo) 
	->
		true
	;
		% for each list of strongly connected components, 
		% perform a fixpoint computation.
		sr_fixpoint_table_init(!.ModuleInfo, !.ReuseTable, 
			SCC, FPtable0), 
		run_with_dependency_until_fixpoint(AliasTable, SCC, FPtable0, 
				!ReuseTable, !ModuleInfo, !IO)
	).

%-----------------------------------------------------------------------------%
:- pred run_with_dependency_until_fixpoint(alias_as_table::in, 
		list(pred_proc_id)::in, sr_fixpoint_table__table::in, 
		reuse_condition_table::in, reuse_condition_table::out, 
		module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.

run_with_dependency_until_fixpoint(AliasTable, 
		SCC, FPtable0, !ReuseTable, !ModuleInfo, !IO) :- 
	list__foldl3(analyse_pred_proc(AliasTable, !.ReuseTable), 
			SCC, !ModuleInfo, FPtable0, FPtable, !IO),
	(
		sr_fixpoint_table_all_stable(FPtable)
	->
		list__foldl(update_goal_in_reuse_table(FPtable), SCC,
				!ReuseTable) 
	;
		sr_fixpoint_table_new_run(FPtable, 
				FPtable1),
		run_with_dependency_until_fixpoint(AliasTable, 
				SCC, FPtable1, !ReuseTable, 
				!ModuleInfo, !IO)
	).

:- pred update_goal_in_reuse_table(sr_fixpoint_table__table::in, 
		pred_proc_id::in, reuse_condition_table::in,
		reuse_condition_table::out) is det.

update_goal_in_reuse_table(FP, PredProcId, !ReuseTable) :- 
	sr_fixpoint_table_get_final_reuse(PredProcId, Memo, _Goal, FP), 
	reuse_condition_table_set(PredProcId, Memo, !ReuseTable). 

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred maybe_write_fixpoint_table_state(bool::in, string::in, 
		pred_proc_id::in, 
		sr_fixpoint_table__table::in, 
		io__state::di, io__state::uo) is det.

maybe_write_fixpoint_table_state(no, _, _, _, !IO). 
maybe_write_fixpoint_table_state(yes, Description, 
		PredProcId, FP, !IO) :-
	sr_fixpoint_table_get_final_reuse(PredProcId, M, _, FP), 
	(sr_fixpoint_table_is_recursive(FP) -> 
		Rec = "yes"; Rec = "no"),

	(
		M = yes(Conditions) 
	-> 
		list__length(Conditions, Length), 
		string__int_to_string(Length, LengthS), 
		string__append_list(
				["%\tNumber of conditions (", 
				Description, "):\t",
				LengthS, "\n"], Msg2),
		write_string(Msg2, !IO)
	; 
		write_string("%\tNo reuse.\n", !IO)
	),
	write_string("%\t\trec = ", !IO),
	write_string(Rec, !IO),
	write_string("\n", !IO).
	
:- pred analyse_pred_proc(alias_as_table::in, 
		reuse_condition_table::in, 
		pred_proc_id::in, 
		module_info::in, module_info::out, 
		sr_fixpoint_table__table::in, sr_fixpoint_table__table::out, 
		io__state::di, io__state::uo) is det.

analyse_pred_proc(AliasTable, ReuseTable, PredProcId, !ModuleInfo, !FP, !IO) :- 
	module_info_pred_proc_info(!.ModuleInfo, PredProcId, 
		PredInfo0, ProcInfo0),
	PredProcId = proc(PredId, ProcId),

	sr_fixpoint_table_which_run(!.FP, Run), 
	string__int_to_string(Run, SRun), 
	string__append_list([ 
		"% Indirect reuse analysing (run ", SRun, ") "],
		Msg),
	passes_aux__write_proc_progress_message(Msg, 
		PredId, ProcId, !.ModuleInfo, !IO), 

	globals__io_lookup_bool_option(very_verbose, VeryVerbose, !IO), 
	maybe_write_fixpoint_table_state(VeryVerbose, "before", 
			PredProcId, !.FP, !IO), 

	% initialize all the necessary information to get the
	% analysis started.
	% 1. get ProcInfo
	%	OK
	% 2. get Goal
	proc_info_goal(ProcInfo0, Goal0),
	%   	OK
	% 3. initialize alias-information
	pa_alias_as__init(Alias0),
	%	OK
	% 4. initialize reuses-information
	hlds_pred__proc_info_headvars(ProcInfo0, HVs), 
	% do not change the state of the fixpoint table by
	% simply consulting it now for initialization.
	sr_fixpoint_table_get_final_reuse(PredProcId, 
			MemoStarting, _, !.FP),
	indirect_reuse_pool_init(HVs, MemoStarting, Pool0),

	% 5. analyse_goal
	analyse_goal(ProcInfo0, !.ModuleInfo, 
		AliasTable, ReuseTable, Goal0, Goal,
		analysis_info(Alias0, Pool0, set__init, !.FP),
		analysis_info(_Alias, Pool, _Static, !:FP), !IO),

	% 	OK
	% 6. update all kind of information
	indirect_reuse_pool_get_memo_reuse(Pool, Memo), 
	sr_fixpoint_table_new_reuse(PredProcId,
				Memo, Goal, !FP),

	maybe_write_fixpoint_table_state(VeryVerbose, "after", 
		PredProcId, !.FP, !IO),
		
	% Update the ProcInfo, PredInfo, hence also ModuleInfo:
	proc_info_set_goal(ProcInfo0, Goal, ProcInfo), 
	module_info_set_pred_proc_info(!.ModuleInfo, PredProcId, 
		PredInfo0, ProcInfo, !:ModuleInfo). 

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- type analysis_info
	--->	analysis_info(
			alias	:: alias_as,
			pool	:: indirect_reuse_pool,
			static	:: set(prog_var),
			table	:: sr_fixpoint_table__table
		).

:- pred debug_write_rec_table(string::in, sr_fixpoint_table__table::in, 
	io__state::di, io__state::uo) is det.
debug_write_rec_table(Msg, Table) --> 
	globals__io_lookup_bool_option(very_verbose, VeryVerbose),
	( 
		{ VeryVerbose = no }
	-> 
		[]
	;
		{ (sr_fixpoint_table_is_recursive(Table) -> 
			R = "yes"
		;	R = "no" ) }, 
		{ string__append_list(
			["%\t\t", Msg, ": R = ", R, ".\n"], Msg2) },
		io__write_string(Msg2)
	).

:- pred analyse_goal(proc_info::in, module_info::in, alias_as_table::in, 
		reuse_condition_table::in, 
		hlds_goal::in, hlds_goal::out,
		analysis_info::in, analysis_info::out,
		io__state::di, io__state::uo) is det.

analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = conj(Goals0), 
	list__map_foldl2(analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable), 
			Goals0, Goals, 
			!AnalysisInfo, !IO), 
	Expr = conj(Goals),
	Info = Info0,
	Goal = Expr - Info. 

analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = call(PredId, ProcId, ActualVars, _, _, _), 
	AnalysisInfo0 = !.AnalysisInfo, 
	passes_aux__write_proc_progress_message(
			"%\t\tcall to ",
			PredId, ProcId, HLDS, !IO), 
	proc_info_vartypes(ProcInfo, VarTypes),
	list__map(
		map__lookup(VarTypes), 
		ActualVars,
		ActualTypes), 
	call_verify_reuse(ProcInfo, HLDS, ReuseTable, 
			PredId, ProcId, ActualVars, 
			ActualTypes, Info0, Info, !AnalysisInfo, _, !IO), 
	pa_run__extend_with_call_alias(HLDS, ProcInfo, AliasTable, 
		PredId, ProcId, ActualVars, ActualTypes, 
			AnalysisInfo0 ^ alias, Alias),
	!:AnalysisInfo = !.AnalysisInfo ^ alias := Alias,
	Expr = Expr0, 
	Goal = Expr - Info.

analyse_goal(_ProcInfo, _HLDS, _AliasTable, _ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = generic_call(_, _, _, _), 
	pa_alias_as__top("unhandled goal", Alias), 
	!:AnalysisInfo = !.AnalysisInfo ^ alias := Alias,
	Goal = Expr0 - Info0.

analyse_goal(ProcInfo, HLDS, _AliasTable, _ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = unify(_Var, _Rhs, _Mode, Unification, _Context), 

		% Record the statically constructed variables.
	( Unification = construct(Var, _, _, _,
			construct_statically(_), _, _) ->
		!:AnalysisInfo = !.AnalysisInfo ^ static 
			:= set__insert(!.AnalysisInfo ^ static, Var)
	;
		true
	),
	pa_alias_as__extend_unification(HLDS, ProcInfo, 
			Unification, Info, !.AnalysisInfo ^ alias, 
			Alias),	
	!:AnalysisInfo = !.AnalysisInfo ^ alias := Alias,
	Info = Info0,
	Expr = Expr0, 
	Goal = Expr - Info.

analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = switch(Var, CanFail, Cases0),
	AI0 = !.AnalysisInfo, 
	list__map_foldl2(
		(pred(case(ConsId, Gin)::in, Tuple::out,
				FPin::in, FPout::out, 
				IOin::di, IOout::uo) is det :-
			analyse_goal(ProcInfo, HLDS, AliasTable, 
				ReuseTable, Gin, Gout, 
				analysis_info(AI0 ^ alias, AI0 ^ pool,
						AI0 ^ static, FPin),
				analysis_info(NewAlias,
						NewPool, NewStatic, FPout),
				IOin, IOout),
			Tuple = { case(ConsId, Gout), NewAlias, NewPool,
					NewStatic }
		),
		Cases0, Tuples,
		AI0 ^ table, FP, !IO),

	Cases = list__map((func({C, _A, _P, _S}) = C), Tuples),
	ListPools = list__map((func({_G, _A, P, _S}) = P), Tuples),
	ListAliases = list__map((func({_G, A, _P, _S}) = A), Tuples),
	ListStatic = list__map((func({_G, _A, _P, S}) = S), Tuples),

	indirect_reuse_pool_least_upper_bound_disjunction(
				ListPools,
				Pool),
	pa_alias_as__least_upper_bound_list(HLDS, ProcInfo, Info0, 
				ListAliases,
				Alias1),
	set__power_union(set__list_to_set(ListStatic), Static),

	% reduce the aliases
	project_on_live_vars(ProcInfo, Info0, Alias1, Alias),

	!:AnalysisInfo = analysis_info(Alias, Pool, Static, FP),

	Info = Info0,
	Expr = switch(Var, CanFail, Cases),
	Goal = Expr - Info. 

analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = disj(Goals0),
	(
		Goals0 = []
	->
		Goals = Goals0
	;
		% XXX up to here
		AI0 = !.AnalysisInfo, 
		list__map_foldl2(
			(pred(Gin::in, Tuple::out,
					FPin::in, FPout::out,
					IOin::di, IOout::uo) is det :-
				analyse_goal(ProcInfo, HLDS, AliasTable, 
						ReuseTable, 
						Gin, Gout, 
					analysis_info(AI0 ^ alias, AI0 ^ pool,
							AI0 ^ static, FPin),
					analysis_info(NewAlias, NewPool,
							NewStatic, FPout),
					IOin,IOout),
				Tuple = { Gout, NewAlias, NewPool, NewStatic }
			),
			Goals0, Tuples,
			AI0 ^ table, FP, !IO), 

		Goals = list__map((func({G, _A, _P, _S}) = G), Tuples),
		ListPools = list__map((func({_G, _A, P, _S}) = P), Tuples),
		ListAliases = list__map((func({_G, A, _P, _S}) = A), Tuples),
		ListStatic = list__map((func({_G, _A, _P, S}) = S), Tuples),
		set__power_union(set__list_to_set(ListStatic), Static),

		indirect_reuse_pool_least_upper_bound_disjunction(
					ListPools,
					Pool),
		pa_alias_as__least_upper_bound_list(HLDS, ProcInfo, Info0, 
					ListAliases,
					Alias1),

		% reduce the aliases
		pa_alias_as__project_on_live_vars(ProcInfo, Info, Alias1, 
					Alias),

		!:AnalysisInfo = analysis_info(Alias, Pool, Static, FP)
	),

	Info = Info0,
	Expr = disj(Goals),
	Goal = Expr - Info. 

analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = not(NegatedGoal0),
	analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable, 
		NegatedGoal0, NegatedGoal, !AnalysisInfo, !IO), 
	Info = Info0, 
	Expr = not(NegatedGoal),
	Goal = Expr - Info. 

analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = some(A, B, SomeGoal0), 
	analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable, SomeGoal0, 
			SomeGoal, !AnalysisInfo, !IO), 
	Info = Info0, 
	Expr = some(A, B, SomeGoal), 
	Goal = Expr - Info.

analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable, Expr0 - Info0, 
		Goal, AI0, AI, !IO) :- 
	Expr0 = if_then_else(Vars, Cond0, Then0, Else0),
	analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable,  
			Cond0, Cond, AI0, AI_Cond, !IO), 
	analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable,  
			Then0, Then, AI_Cond, AI_Then, !IO), 

	AI1 = AI0 ^ table := AI_Then ^ table,
	analyse_goal(ProcInfo, HLDS, AliasTable, ReuseTable,  
			Else0, Else, AI1, AI_Else, !IO), 

	indirect_reuse_pool_least_upper_bound_disjunction(
				[AI_Then ^ pool, AI_Else ^ pool],
				Pool),

	pa_alias_as__least_upper_bound_list(HLDS, ProcInfo, Info0, 
				[AI_Then ^ alias, AI_Else ^ alias],
				Alias1),
	Static = AI_Then ^ static `set__union` AI_Else ^ static,
	
	% reduce the aliases
	goal_info_get_outscope(Info, Outscope),
	pa_alias_as__project_set(Outscope, Alias1, Alias),

	AI = analysis_info(Alias, Pool, Static, AI_Else ^ table),

	Info = Info0,
	Expr = if_then_else(Vars, Cond, Then, Else),
	Goal = Expr - Info.

analyse_goal(ProcInfo, HLDS, _AliasTable, _ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = foreign_proc(Attrs, PredId, ProcId, 
					Vars, MaybeModes, Types, _), 
	pa_alias_as__extend_foreign_code(HLDS, ProcInfo, Attrs, 
			PredId, ProcId, Vars, 
			MaybeModes, Types, Info0, 
			!.AnalysisInfo ^ alias, Alias),
	!:AnalysisInfo = !.AnalysisInfo ^ alias := Alias,
	Goal = Expr0 - Info0.

analyse_goal(_ProcInfo, _HLDS, _AliasTable, _ReuseTable, Expr0 - Info0, 
		Goal, !AnalysisInfo, !IO) :- 
	Expr0 = par_conj(_), 
	pa_alias_as__top("unhandled goal (par_conj)", Alias), 
	!:AnalysisInfo = !.AnalysisInfo ^ alias := Alias,
	Goal = Expr0 - Info0.

analyse_goal(_ProcInfo, _HLDS, _AliasTable, _ReuseTable, Expr0 - _Info0, 
		_Goal, !AnalysisInfo, !IO) :- 
	Expr0 = shorthand(_), 
	error("sr_indirect__analyse_goal: shorthand goal").

:- pred call_verify_reuse(proc_info::in, module_info::in,
		reuse_condition_table::in, 
		pred_id::in, proc_id::in, list(prog_var)::in,
		list((type))::in, 
		hlds_goal_info::in, hlds_goal_info::out, 
		analysis_info::in, analysis_info::out, bool::out, 
		io__state::di, io__state::uo) is det.

call_verify_reuse(ProcInfo, ModuleInfo, ReuseTable, 
		PredId, ProcId, ActualVars, ActualTypes, 
		GoalInfo0, GoalInfo, analysis_info(Alias0, Pool0, Static, FP0),
		analysis_info(Alias0, Pool, Static, FP), YesNo) -->
	call_verify_reuse(ProcInfo, ModuleInfo, ReuseTable, 
			PredId, ProcId, ActualVars,
			ActualTypes, 
			Alias0, Static, Pool0, Pool, GoalInfo0, GoalInfo,
			FP0, FP, YesNo).

:- pred call_verify_reuse(proc_info::in, module_info::in, 
		reuse_condition_table::in, pred_id::in,
		proc_id::in, list(prog_var)::in, list((type))::in, 
		alias_as::in,
		set(prog_var)::in, indirect_reuse_pool::in,
		indirect_reuse_pool::out, hlds_goal_info::in ,
		hlds_goal_info::out, sr_fixpoint_table__table::in,
		sr_fixpoint_table__table::out, bool::out, 
		io__state::di, io__state::uo) is det.

call_verify_reuse(ProcInfo, HLDS, ReuseTable, PredId0, ProcId0, 
			ActualVars, ActualTypes, Alias0, 
			StaticTerms, Pool0, Pool, 
			Info0, Info, FP0, FP, YesNo, IO0, IO) :- 

	module_info_structure_reuse_info(HLDS, ReuseInfo),
	ReuseInfo = structure_reuse_info(ReuseMap),
	(map__search(ReuseMap, proc(PredId0, ProcId0), Result) ->
		Result = proc(PredId, ProcId) - _Name,
		passes_aux__write_proc_progress_message(
				"%\t\tSuccess lookup in reuse map: ",
				PredId, ProcId, HLDS, IO0, IO2)
	;
		PredId = PredId0,
		ProcId = ProcId0,
		IO2 = IO0
	),

	% 0. fetch the procinfo of the called procedure:
	module_info_pred_proc_info(HLDS, PredId, ProcId, PredInfo, 
					ProcInfo0),
	% 1. find the tabled reuse for the called predicate
	lookup_memo_reuse(PredId, ProcId, HLDS, ReuseTable, FP0, FP,
					FormalMemo, IO2, IO),	
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
		proc_info_headvars(ProcInfo0, FormalVars), 
		pred_info_arg_types(PredInfo, FormalTypes),
		memo_reuse_rename(
			map__from_corresponding_lists(FormalVars, ActualVars),
			yes(to_type_renaming(FormalTypes, ActualTypes)), 
			FormalMemo, Memo), 
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
		LUiData = set__map(pa_datastruct__init, LUi),
		pa_alias_as__live(HLDS, ProcInfo, LUiData, 
			LIVE0, Alias0, Live_i),
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
			goal_info_set_reuse(KindReuse, Info0, Info),
			YesNo = yes
		;
			Pool = Pool0,
	
			examine_cause_of_missed_reuse(HLDS, ProcInfo, 
					LFUi, LBUi, 
					StaticTerms, Memo, 
					Cause), 
			
			goal_info_set_reuse(
				potential_reuse(missed_reuse_call(Cause)), 
				Info0, 
				Info), 
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
			set__map(pa_datastruct__init, LFU), 
			DummyLive, BottomAlias, LFU_Live), 
	pa_alias_as__live(ModuleInfo, ProcInfo, 
			set__map(pa_datastruct__init, LBU), 
			DummyLive, BottomAlias, LBU_Live), 
	Condition = condition(Nodes, _LU, _LA), 
	% 
	NodesL = set__to_sorted_list(Nodes),
	(
		% check whether reason for no reuse is StaticVars
		list__filter_map(
			(pred(Node::in, Var::out) is semidet :- 
				Var = Node^sc_var, 
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
:- pred lookup_memo_reuse(pred_id::in, proc_id::in, module_info::in, 
		reuse_condition_table::in, 
		sr_fixpoint_table__table::in, sr_fixpoint_table__table::out, 
		memo_reuse::out, io__state::di, io__state::uo) is det.

	% similar to the lookup_call_alias from pa_run:
	% 1. check in fixpoint table
	% 2. check in module_info (already fully analysed or imported pred)
	%    no special treatment necessary for primitive predicates and
	%    alike, as the default of predicates is no reuse anyway.
lookup_memo_reuse(PredId, ProcId, HLDS, ReuseTable, !FP, Memo, !IO) :- 
	PredProcId = proc(PredId, ProcId),
	(
		% 1 - check in table
		sr_fixpoint_table_get_reuse(PredProcId, 
					Memo1, !FP)
	->
		( sr_fixpoint_table_is_recursive(!.FP) -> R = "yes"; R = "no"),
		string__append_list(
			["%\t\tsucceeded fpt (R = ", R, ") for "], Msg),
		passes_aux__write_proc_progress_message(Msg,
			PredId, ProcId, HLDS, !IO),
		Memo = Memo1
	;
		passes_aux__write_proc_progress_message(
			"%\t\tfailed fpt lookup for ", 
			PredId, ProcId, HLDS, !IO), 
		% 2 - lookup in reuse table
		Memo1 = reuse_condition_table_search(PredProcId, ReuseTable)
	-> 
		Memo = Memo1
	; 
		passes_aux__write_proc_progress_message(
			"%\t\tfailed reuse_table lookup for ", 
			PredId, ProcId, HLDS, !IO), 
		Memo = no
		
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
		pa_alias_as__normalize(HLDS, ProcInfo, InstMap0, 
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



	


