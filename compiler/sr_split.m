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

	% create_multiple_versions( VirginHLDS, ReuseHLDS, FinalHLDS ).
	% Starting from the VirginHLDS, it computes a new HLDS where for
	% each procedure having conditional reuse (ReuseHLDS), a new
	% separate reuse-procedure is added. The calls can then also 
	% be corrected so that they point to the correct reuse-versions.
:- pred sr_split__create_multiple_versions( module_info::in, module_info::in,
		module_info::out, io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module std_util, require, list, set, map.
:- import_module dependency_graph, hlds_pred. 
:- import_module hlds_goal, prog_data, hlds_data, prog_util. 
:- import_module sr_data. 


sr_split__create_multiple_versions( VirginHLDS, ReuseHLDS, HLDS) --> 
		% compute the strongly connected components
	{ module_info_ensure_dependency_info( ReuseHLDS, ReuseHLDS1) },
	{ module_info_get_maybe_dependency_info( ReuseHLDS1, MaybeDepInfo) } ,
	(
		{ MaybeDepInfo = yes(DepInfo) }
	->
		{ hlds_dependency_info_get_dependency_ordering( DepInfo,
				DepOrdering ) },
		run_with_dependencies( DepOrdering, ReuseHLDS1, 
					VirginHLDS, HLDS)
	;
		{ error("(sr_split) create_multiple_versions: no dependency info") }
	).

:- pred run_with_dependencies( dependency_ordering, module_info, module_info,
					module_info, io__state, io__state).
:- mode run_with_dependencies( in, in, in, out, di, uo) is det.

run_with_dependencies( Deps, ReuseHLDSin, VirginHLDS, HLDSout) -->
	list__foldl2( run_with_dependency(VirginHLDS), Deps, 
				ReuseHLDSin, HLDSout ).

:- pred run_with_dependency( module_info, list(pred_proc_id), 
				module_info, module_info,
				io__state, io__state).
:- mode run_with_dependency( in, in, in, out, di, uo ) is det.

run_with_dependency( VirginHLDS, SCC , HLDSin, HLDSout ) -->
	{ list__foldl( create_versions(VirginHLDS), 
			SCC, 
			HLDSin,
			HLDSout ) }.

:- pred create_versions( module_info::in, pred_proc_id::in, 
		module_info::in, module_info::out) is det.

create_versions( VirginHLDS, PredProcId, WorkingHLDS, HLDS):- 
	module_info_pred_proc_info( WorkingHLDS, PredProcId, 
				PredInfo0, ProcInfo0),
	proc_info_reuse_information( ProcInfo0, Memo), 
	module_info_pred_proc_info( VirginHLDS, PredProcId, _, 
				CleanProcInfo), 

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
			proc_info_goal( ProcInfo0, ReuseGoal), 
			create_reuse_pred(Memo, yes(ReuseGoal), 
					PredInfo0, ProcInfo0,
					ReusePredInfo, ReuseProcInfo0,
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
			process_goal( ReuseGoal, ReuseGoal2, WorkingHLDS2, _),
			proc_info_set_goal( ReuseProcInfo0, ReuseGoal2, 
					ReuseProcInfo1), 
			module_info_set_pred_proc_info( WorkingHLDS2, 
					ReusePredId, ReuseProcId, 
					ReusePredInfo, ReuseProcInfo1, 
					WorkingHLDS3), 

			% and put a clean procedure back in place 
			module_info_set_pred_proc_info( WorkingHLDS3,
				PredProcId, PredInfo0, CleanProcInfo, HLDS)
		;
			% memo_reuse is unconditional -- perfect -- 
			% nothing to be done! 
			HLDS = WorkingHLDS
		)
	).

	

:- pred create_reuse_pred(memo_reuse::in, maybe(hlds_goal)::in,
		pred_info::in, proc_info::in,
		pred_info::out, proc_info::out,
		proc_id::out, sym_name::out) is det.

create_reuse_pred(TabledReuse, MaybeReuseGoal, PredInfo, ProcInfo,
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

	Line = 0,
	Counter = 0,

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
