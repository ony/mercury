%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
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

:- module sr_split.
:- interface.

:- import_module hlds_module, io.
:- import_module hlds_pred, sr_data, std_util, hlds_goal.

	% create_multiple_versions( VirginHLDS, ReuseHLDS, FinalHLDS ).
	% Starting from the VirginHLDS, it computes a new HLDS where for
	% each procedure having conditional reuse (ReuseHLDS), a new
	% separate reuse-procedure is added. The calls can then also 
	% be corrected so that they point to the correct reuse-versions.
:- pred sr_split__create_multiple_versions( module_info::in, module_info::in,
		module_info::out, io__state::di, io__state::uo) is det.

:- pred create_reuse_pred(pred_proc_id::in, memo_reuse::in,
		maybe(hlds_goal)::in,
		module_info::in, module_info::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module std_util, require, list, set, map.
:- import_module hlds_pred. 
:- import_module hlds_goal, prog_data, hlds_data, prog_util. 
:- import_module sr_data. 


sr_split__create_multiple_versions( VirginHLDS, ReuseHLDS, HLDS) --> 
		% compute the strongly connected components
	{ create_versions( VirginHLDS, ReuseHLDS, HLDS1) },
	{ reprocess_all_goals( HLDS1, HLDS ) }.

	% reprocess each of the procedures to make sure that all calls
	% to reuse preds are correct. 
:- pred reprocess_all_goals(module_info::in, module_info::out) is det.

reprocess_all_goals( HLDS0, HLDS ) :- 
	module_info_predids( HLDS0, PredIds), 
	list__foldl(
		reprocess_all_goals_2,
		PredIds,
		HLDS0, 
		HLDS).

:- pred reprocess_all_goals_2( pred_id::in, module_info::in, 
		module_info::out ) is det. 
reprocess_all_goals_2( PredId, HLDS0, HLDS ) :- 
	module_info_pred_info( HLDS0, PredId, PredInfo0 ), 
	pred_info_procids( PredInfo0, ProcIds ), 
	pred_info_procedures( PredInfo0, Procedures0 ), 
	list__foldl(
		reprocess_all_goals_3(HLDS0),
		ProcIds,
		Procedures0, 
		Procedures
		), 
	pred_info_set_procedures( PredInfo0, Procedures, PredInfo), 
	module_info_set_pred_info( HLDS0, PredId, PredInfo, HLDS ). 

:- pred reprocess_all_goals_3( module_info::in, proc_id::in, 
		proc_table::in, proc_table::out) is det.
reprocess_all_goals_3( HLDS, ProcId, ProcTable0, ProcTable) :- 
	map__lookup( ProcTable0, ProcId, ProcInfo0), 
	proc_info_reuse_information( ProcInfo0 , Memo ), 
	(
		Memo = yes(_)
	->
		proc_info_goal( ProcInfo0, Goal0), 
		process_goal( Goal0, Goal, HLDS, _ ), 
		proc_info_set_goal( ProcInfo0, Goal, ProcInfo), 
		map__det_update( ProcTable0, ProcId, ProcInfo, ProcTable)
	;
		ProcTable = ProcTable0
	).


:- pred create_versions( module_info, module_info, module_info).
:- mode create_versions( in, in, out) is det.

create_versions( VirginHLDS, ReuseHLDS, HLDS) :- 
	module_info_predids( ReuseHLDS, PredIds), 
	list__foldl(
		create_versions_2(VirginHLDS),
		PredIds,
		ReuseHLDS, 
		HLDS).

:- pred create_versions_2( module_info::in, pred_id::in, 
			module_info::in, module_info::out) is det.

create_versions_2( VirginHLDS, PredId , HLDS0, HLDS ) :- 
	module_info_pred_info( HLDS0, PredId, PredInfo0 ), 
	pred_info_procids( PredInfo0, ProcIds ), 
	list__foldl(
		pred( Id::in, H0::in, H::out ) is det :- 
		(
			create_versions_3( VirginHLDS, 
				proc(PredId, Id), 
				H0, H)
		),
		ProcIds,
		HLDS0,
		HLDS
	).

:- pred create_versions_3( module_info::in, pred_proc_id::in, 
		module_info::in, module_info::out) is det.

create_versions_3( VirginHLDS, PredProcId, WorkingHLDS, HLDS):- 
	module_info_pred_proc_info( WorkingHLDS, PredProcId, 
				PredInfo0, ProcInfo0),
	proc_info_reuse_information( ProcInfo0, Memo), 
	module_info_pred_proc_info( VirginHLDS, PredProcId, _, 
				CleanProcInfo), 
	proc_info_goal( ProcInfo0, ReuseGoal), 

	(
		Memo = no
	-> 
		% restore the old status of the procedure
		module_info_set_pred_proc_info( WorkingHLDS, PredProcId,
				PredInfo0, CleanProcInfo, HLDS)
	;
		( 
			memo_reuse_is_conditional(Memo) 
		->
			% fetch the reuse goal

			create_reuse_pred(Memo, PredProcId, yes(ReuseGoal), 
					PredInfo0, ProcInfo0,
					ReusePredInfo, _ReuseProcInfo0,
					ReuseProcId, ReuseName),
			module_info_get_predicate_table(WorkingHLDS,
					PredTable0),
			module_info_structure_reuse_info(WorkingHLDS,
					StrReuseInfo0),
			StrReuseInfo0 = structure_reuse_info(ReuseMap0),
			predicate_table_insert(PredTable0, ReusePredInfo,
					ReusePredId, PredTable),
			map__det_insert(ReuseMap0, PredProcId,
				proc(ReusePredId, ReuseProcId) - ReuseName,
				ReuseMap),
			StrReuseInfo = structure_reuse_info(ReuseMap),
			module_info_set_structure_reuse_info(WorkingHLDS,
					StrReuseInfo, WorkingHLDS1),
			module_info_set_predicate_table(WorkingHLDS1, 
					PredTable, WorkingHLDS2),

			% reprocess the goal
			% this has moved to an extra little pass. 

			% and put a clean procedure back in place 
			module_info_set_pred_proc_info( WorkingHLDS2,
				PredProcId, PredInfo0, CleanProcInfo, HLDS)
		;
			% memo_reuse is unconditional -- perfect -- 
			% nothing to be done! (processing the goal is
			% done separately). 
			HLDS = WorkingHLDS

		)
	).

	
create_reuse_pred(PRED_PROC_ID, TREUSE, MaybeHLDS_GOAL, HLDSin, HLDSout) :-
	module_info_pred_proc_info(HLDSin, PRED_PROC_ID, PredInfo0, 
					ProcInfo0),
	( memo_reuse_is_conditional(TREUSE) ->
		create_reuse_pred(TREUSE, PRED_PROC_ID,
				MaybeHLDS_GOAL, PredInfo0, ProcInfo0,
				ReusePredInfo, _ReuseProcInfo,
				ReuseProcId, ReuseName),

		module_info_get_predicate_table(HLDSin, PredTable0),
		predicate_table_insert(PredTable0, ReusePredInfo,
				ReusePredId, PredTable),
		module_info_structure_reuse_info(HLDSin, StrReuseInfo0),
		StrReuseInfo0 = structure_reuse_info(ReuseMap0),
		map__det_insert(ReuseMap0, PRED_PROC_ID,
				proc(ReusePredId, ReuseProcId) - ReuseName,
				ReuseMap),
		StrReuseInfo = structure_reuse_info(ReuseMap),
		module_info_set_structure_reuse_info(HLDSin,
				StrReuseInfo, HLDSin1),
		module_info_set_predicate_table(HLDSin1, PredTable, HLDSout)
	% ; contains_unconditional_reuse(TREUSE) ->
	;
		proc_info_set_reuse_information(ProcInfo0, 
						TREUSE, ProcInfo1),
		(
			MaybeHLDS_GOAL = yes(HLDS_GOAL),
			proc_info_set_goal(ProcInfo1, HLDS_GOAL, ProcInfo)
		;
			MaybeHLDS_GOAL = no,
			ProcInfo = ProcInfo1
		),
		module_info_set_pred_proc_info(HLDSin, PRED_PROC_ID, 
				PredInfo0, ProcInfo, HLDSout)
	).

:- pred create_reuse_pred(memo_reuse::in, pred_proc_id::in,
		maybe(hlds_goal)::in, pred_info::in, proc_info::in,
		pred_info::out, proc_info::out,
		proc_id::out, sym_name::out) is det.

create_reuse_pred(TabledReuse, PredProcId, MaybeReuseGoal, PredInfo, ProcInfo,
		ReusePredInfo, ReuseProcInfo, ReuseProcId, SymName) :-
	proc_info_set_reuse_information(ProcInfo, 
				TabledReuse, ReuseProcInfo0),
	(
		MaybeReuseGoal = yes(ReuseGoal),
		proc_info_set_goal(ReuseProcInfo0, ReuseGoal, ReuseProcInfo)
	;
		MaybeReuseGoal = no,
		ReuseProcInfo = ReuseProcInfo0
	),
	pred_info_module(PredInfo, ModuleName),
	pred_info_name(PredInfo, Name),
	pred_info_arg_types(PredInfo, TypeVarSet, ExistQVars, Types),
	Cond = true,
	pred_info_context(PredInfo, PredContext),
	pred_info_import_status(PredInfo, Status),
	pred_info_get_markers(PredInfo, Markers),
	pred_info_get_is_pred_or_func(PredInfo, PredOrFunc),
	pred_info_get_class_context(PredInfo, ClassContext),
	pred_info_get_aditi_owner(PredInfo, Owner),

	set__init(Assertions),

	PredProcId = proc(_PredId, ProcId),
	proc_id_to_int(ProcId, ProcIdInt),

	Line = 0,
	Counter = ProcIdInt,

	make_pred_name_with_context(ModuleName, "reuse", PredOrFunc, Name,
		Line, Counter, SymName),

	pred_info_create(ModuleName, SymName, TypeVarSet, ExistQVars, Types,
			Cond, PredContext, Status, Markers, PredOrFunc,
			ClassContext, Owner, Assertions, ReuseProcInfo, 
			ReuseProcId, ReusePredInfo).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
:- pred process_goal(hlds_goal::in, hlds_goal::out,
		module_info::in, module_info::out) is det.

process_goal(Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = call(PredId0, ProcId0, Args, Builtin, MaybeContext, Name0) },
	=(ModuleInfo),
	{ module_info_structure_reuse_info(ModuleInfo, ReuseInfo) },
	{ ReuseInfo = structure_reuse_info(ReuseMap) },
	{
		goal_info_get_reuse(GoalInfo, reuse(reuse_call)),
		map__search(ReuseMap, proc(PredId0, ProcId0), Result)
	->
		Result = proc(PredId, ProcId) - Name
	;
		PredId = PredId0,
		ProcId = ProcId0,
		Name = Name0
	},
	{ Goal = call(PredId, ProcId, Args, Builtin, MaybeContext, Name) }.

process_goal(Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = unify(_Var, _Rhs, _Mode, _Unification0, _Ctxt) },
	{ Goal = Goal0 }.
process_goal(Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = generic_call(_, _, _, _) },
	{ Goal = Goal0 }.
process_goal(Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = pragma_foreign_code(_, _, _, _, _, _, _, _) },
	{ Goal = Goal0 }.
process_goal(Goal0 - _GoalInfo, _) -->
	{ Goal0 = bi_implication(_, _) },
	{ error("structure_reuse: bi_implication.\n") }.

process_goal(Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = if_then_else(Vars, If0, Then0, Else0, SM) },
	process_goal(If0, If),
	process_goal(Then0, Then),
	process_goal(Else0, Else),
	{ Goal = if_then_else(Vars, If, Then, Else, SM) }.

process_goal(Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = switch(Var, CanFail, Cases0, StoreMap) },
	process_goal_cases(Cases0, Cases),
	{ Goal = switch(Var, CanFail, Cases, StoreMap) }.

process_goal(Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = some(Vars, CanRemove, SomeGoal0) },
	process_goal(SomeGoal0, SomeGoal),
	{ Goal = some(Vars, CanRemove, SomeGoal) }.

process_goal(not(Goal0) - GoalInfo, not(Goal) - GoalInfo) -->
	process_goal(Goal0, Goal).
process_goal(conj(Goal0s) - GoalInfo, conj(Goals) - GoalInfo) -->
	process_goal_list(Goal0s, Goals).
process_goal(disj(Goal0s, SM) - GoalInfo, disj(Goals, SM) - GoalInfo) -->
	process_goal_list(Goal0s, Goals).
process_goal(par_conj(Goal0s, SM) - GoalInfo,
		par_conj(Goals, SM) - GoalInfo) -->
	process_goal_list(Goal0s, Goals).

:- pred process_goal_cases(list(case)::in, list(case)::out,
		module_info::in, module_info::out) is det.

process_goal_cases([], []) --> [].
process_goal_cases([Case0 | Case0s], [Case | Cases]) -->
	{ Case0 = case(ConsId, Goal0) },
	process_goal(Goal0, Goal),
	{ Case = case(ConsId, Goal) },
	process_goal_cases(Case0s, Cases).

:- pred process_goal_list(hlds_goals::in, hlds_goals::out,
		module_info::in, module_info::out) is det.

process_goal_list([], []) --> [].
process_goal_list([Goal0 | Goal0s], [Goal | Goals]) -->
	process_goal(Goal0, Goal),
	process_goal_list(Goal0s, Goals).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
