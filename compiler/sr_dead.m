%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_dead
% Main authors: nancy
% 
% Mark each cell that dies with its reuse_condition, and mark each
% construction with the cells that construction could possibly reuse.
% sr_choice is responsible for deciding which cell will actually be
% reused.
%
%-----------------------------------------------------------------------------%

:- module structure_reuse__sr_dead.
:- interface.

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.

:- pred sr_dead__process_goal(pred_id::in, proc_info::in, module_info::in, 
				hlds_goal::in, hlds_goal::out) is det.


%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module hlds__hlds_data.
:- import_module parse_tree__prog_data.
:- import_module possible_alias__pa_alias_as.
:- import_module possible_alias__pa_run.
:- import_module structure_reuse__sr_data.
:- import_module structure_reuse__sr_live.
:- import_module structure_reuse__sr_util.

:- import_module assoc_list, int, require. 
:- import_module set, list, map, std_util.

process_goal(_PredId, ProcInfo, ModuleInfo, Goal0, Goal) :- 
	pa_alias_as__init(Alias0), 
	hlds_pred__proc_info_headvars(ProcInfo, HeadVars), 
	dead_cell_pool_init(HeadVars, Pool0), 
	annotate_goal(ProcInfo, ModuleInfo, Goal0, Goal, 
			Pool0, _Pool, Alias0, _Alias).
		
	
%-----------------------------------------------------------------------------%

:- pred annotate_goal(proc_info::in, module_info::in,
		hlds_goal::in, hlds_goal::out, 
		dead_cell_pool::in, dead_cell_pool::out, 
		alias_as::in, alias_as::out) is det.

annotate_goal(ProcInfo, HLDS, Expr0 - Info0, Goal,
		Pool0, Pool, Alias0, Alias) :- 
	Expr0 = conj(Goals0),
	sr_util__list_map_foldl2(
		annotate_goal(ProcInfo, HLDS),
		Goals0, Goals,
		Pool0, Pool,
		Alias0, Alias),
	Info = Info0, 
	Expr = conj(Goals),
	Goal = Expr - Info. 
	
annotate_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, Alias0, Alias) :- 
	Expr0 = call(PredId, ProcId, ActualVars, _, _, _),
	proc_info_vartypes(ProcInfo, VarTypes), 
	list__map(map__lookup(VarTypes), ActualVars, ActualTypes), 
	pa_run__extend_with_call_alias(HLDS, ProcInfo, 
		PredId, ProcId, ActualVars, ActualTypes, Alias0, Alias),
	Expr = Expr0, 
	Info = Info0, 
	Pool = Pool0, 
	Goal = Expr - Info. 
	
annotate_goal(_ProcInfo, _HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, _Alias0, Alias) :- 
	Expr0 = generic_call(_, _, _, _), 
	Pool = Pool0,
	pa_alias_as__top("unhandled goal", Alias),
	Goal = Expr0 - Info0. 
	
annotate_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, Alias0, Alias) :- 
	Expr0 = switch(A, B, Cases0),
	goal_info_get_outscope(Info0, Outscope), 
	sr_util__list_map3(annotate_case(ProcInfo, HLDS, Pool0, Alias0),
			Cases0, Cases, ListPools, ListAliases),
	dead_cell_pool_least_upper_bound_disj(Outscope, ListPools, Pool), 
	pa_alias_as__least_upper_bound_list(ProcInfo, HLDS, Info0, 
			ListAliases, Alias),
	Info = Info0, 
	Expr = switch(A, B, Cases), 
	Goal = Expr - Info. 
	
annotate_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, Alias0, Alias) :- 
	Expr0 = unify(_Var, _Rhs, _Mode, Unification0, _Context),
	unification_verify_reuse(HLDS, ProcInfo, Unification0, Alias0, 
		Pool0, Pool, Info0, Info),
		% XXX candidate for future optimization: if
		% you annotate the deconstruct first, you might avoid
		% creating the aliases altogether, thus reducing the
		% number of aliases you cary along, and eventually
		% having an impact on the analysis-time.
	pa_alias_as__extend_unification(ProcInfo, HLDS, Unification0,
			Info, Alias0, Alias),
	Expr = Expr0, 
	Goal = Expr - Info. 
	
annotate_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, Alias0, Alias) :- 
	Expr0 = disj(Goals0),
	goal_info_get_outscope(Info0, Outscope), 
	(
		Goals0 = []
	->
		Goals = Goals0, 
		Pool = Pool0, 
		Alias = Alias0
	;
		list_map3(
			pred(Gin::in, Gout::out, P::out, A::out)
				is det :- 
			(
			   annotate_goal(ProcInfo, HLDS, 
				Gin, Gout, Pool0, P, 
				Alias0, A)
			),
			Goals0, Goals, 
			ListPools, ListAliases),
		dead_cell_pool_least_upper_bound_disj(Outscope,
			ListPools, Pool),
		pa_alias_as__least_upper_bound_list(ProcInfo, 
			HLDS, Info0, ListAliases, Alias)
	),
	Info = Info0,
	Expr = disj(Goals),
	Goal = Expr - Info. 
	
annotate_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, Alias0, Alias) :- 
	Expr0 = not(NegatedGoal0),
	annotate_goal(ProcInfo, HLDS, NegatedGoal0, NegatedGoal,
			Pool0, Pool, Alias0, Alias),
	Info = Info0, 
	Expr = not(NegatedGoal),
	Goal = Expr - Info. 
	
annotate_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, Alias0, Alias) :- 
	Expr0 = some(A, B, SomeGoal0),
	% XXX
	annotate_goal(ProcInfo, HLDS, SomeGoal0, SomeGoal, Pool0, Pool, 
			Alias0, Alias), 
	Info = Info0, 
	Expr = some(A, B, SomeGoal),
	Goal = Expr - Info. 
	
annotate_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, Alias0, Alias) :- 
	Expr0 = if_then_else(Vars, Cond0, Then0, Else0),
	goal_info_get_outscope(Info0, Outscope), 
	annotate_goal(ProcInfo, HLDS, Cond0, Cond, Pool0, 
			PoolCond, Alias0, AliasCond),
	annotate_goal(ProcInfo, HLDS, Then0, Then, PoolCond, 
			PoolThen, AliasCond, AliasThen),
	annotate_goal(ProcInfo, HLDS, Else0, Else, Pool0, 
			PoolElse, Alias0, AliasElse), 
	dead_cell_pool_least_upper_bound_disj(Outscope, 
			[ PoolThen, PoolElse ], Pool), 
	pa_alias_as__least_upper_bound_list(ProcInfo, HLDS, Info0, 
			[ AliasThen, AliasElse ], Alias),
	Info = Info0, 
	Expr = if_then_else(Vars, Cond, Then, Else),
	Goal = Expr - Info. 
	
annotate_goal(ProcInfo, HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, Alias0, Alias) :- 
	Expr0 = foreign_proc(Attrs, PredId, ProcId, 
			Vars, MaybeModes, Types, _), 
	extend_foreign_code(HLDS, ProcInfo, Attrs, PredId, ProcId, 
		Vars, MaybeModes, Types, Info0, Alias0, Alias), 
	Pool = Pool0, 
	Goal = Expr0 - Info0. 
	
annotate_goal(_ProcInfo, _HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, _Alias0, Alias) :- 
	Expr0 = par_conj(_),
	Pool = Pool0,
	pa_alias_as__top("unhandled goal", Alias),
	Goal = Expr0 - Info0. 
		
annotate_goal(_ProcInfo, _HLDS, Expr0 - Info0, Goal, 
			Pool0, Pool, _Alias0, Alias) :- 
	Expr0 = shorthand(_),
	Pool = Pool0,
	pa_alias_as__top("unhandled goal", Alias),
	Goal = Expr0 - Info0. 


:- pred annotate_case(proc_info::in, module_info::in,
		dead_cell_pool::in, alias_as::in, case::in,
		case::out, dead_cell_pool::out, alias_as::out) is det.

annotate_case(ProcInfo, HLDS, Pool0, Alias0, Case0, Case, Pool, Alias) :- 
	Case0 = case(ConsId, Goal0),
	annotate_goal(ProcInfo, HLDS, Goal0, Goal, Pool0, Pool, Alias0, Alias), 
	Case = case(ConsId, Goal).

:- pred unification_verify_reuse(module_info::in, proc_info::in, 
		hlds_goal__unification::in, 
		alias_as::in, dead_cell_pool::in, dead_cell_pool::out,
		hlds_goal_info::in, hlds_goal_info::out) is det.

unification_verify_reuse(ModuleInfo, ProcInfo, Unification, Alias0,
		Pool0, Pool, Info0, Info) :- 
	(
		Unification = deconstruct(Var, ConsId, Vars, _, _, _)
	->
		goal_info_get_lfu(Info0, LFU), 
		goal_info_get_lbu(Info0, LBU),
		set__union(LFU, LBU, LU), 
		sr_live__init(Live0),
		pa_alias_as__live(ModuleInfo, ProcInfo, LU, Live0, 
				Alias0, Live), 
		(
			(
				% XXX things suchs as pred_const's cannot
				% die. 
				cons_id_maybe_arity(ConsId, no)
			;
				% Do not consider functors of arity 0
				% dead. 
				cons_id_arity(ConsId, 0)
			;
				sr_live__is_live(Var, Live) 
			;
				pa_alias_as__is_top(Alias0)
			)
		
		->
			goal_info_set_reuse( choice(deconstruct(no)), 
				Info0, Info),
			Pool = Pool0
		;
			add_dead_cell(ModuleInfo, ProcInfo, 
					Var, list__length(Vars), 
					LFU, LBU,
					Alias0, Pool0, Pool, 
					ReuseCondition),
			goal_info_set_reuse(
				choice(deconstruct(
					yes(ReuseCondition))), Info0, Info) 
		)
	;
		Unification = construct(_, ConsId, Vars, _, _, _, _)
	->
			% XXX to avoid trying to reuse cells such as
			% pred_const, which don't have a valid cons_id
			% passed to them in ml_gen_new_object. ie
			% pred_const's.
			% Do not reuse cells for constructing functors
			% of arity zero. 
		( 
			( cons_id_maybe_arity(ConsId, no) ; 
			  cons_id_arity(ConsId, 0) )
		->
			set__init(ReuseVarsConds)
		;
			dead_cell_pool_try_to_reuse(list__length(Vars),
					Pool0, ReuseVarsConds)
		),
		goal_info_set_reuse(choice(construct(ReuseVarsConds)),
				Info0, 
				Info),
		Pool = Pool0
	;
		% assign
		% simple_test
		% complicated_unify
		Pool = Pool0,
		Info = Info0
	).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

	% type used for threading through all the information about
	% eventual dead cells.
:- type dead_cell_pool ---> 
		pool(
			list(prog_var), % real headvars
			map(prog_var, dead_extra_info)
		).

	% for each dead cell, we need to keep it's reuse-condition,
	% and during this phase, fill in the names of all the vars
	% who would be interested in reusing the dead cell. 
:- type dead_extra_info --->
		extra(
			int, 		% the number of variables in the
					% cell, note that is different
					% to the arity of the cell.
					% ie type_info's, existentially
					% typed data constructors
			reuse_condition, 
			list(prog_var) 	% XXX for the moment always kept
					% empty
		).

	% initialize dr_info	
:- pred dead_cell_pool_init(list(prog_var)::in, dead_cell_pool::out) is det.
	% test if empty
:- pred dead_cell_pool_is_empty(dead_cell_pool::in) is semidet.

:- pred add_dead_cell(module_info, proc_info, prog_var, int, set(prog_var), 
			set(prog_var), alias_as, 
			dead_cell_pool, dead_cell_pool, 
			reuse_condition).
:- mode add_dead_cell(in, in, in, in, in, in, in, in, out, out) is det.

	% given its reuse_condition, add the dead cell to dr_info.
:- pred add_dead_cell(prog_var, int, reuse_condition, 
			dead_cell_pool, dead_cell_pool) is det.
:- mode add_dead_cell(in, in, in, in, out) is det.

:- pred dead_cell_pool_least_upper_bound_disj(set(prog_var),
				list(dead_cell_pool), dead_cell_pool).
:- mode dead_cell_pool_least_upper_bound_disj(in, in, out) is det.

:- pred dead_cell_pool_least_upper_bound(dead_cell_pool, 
				dead_cell_pool,
				dead_cell_pool).
:- mode dead_cell_pool_least_upper_bound(in, in, out) is det.

	% given the set of currently non-local vars (all vars that
	% are in fact nonlocal, including the ones that were not 
	% used within the goal that we are leaving), update the 
	% dr_info::current_scope field. 
:- pred dead_cell_pool_leave_scope(set(prog_var), dead_cell_pool, 
					dead_cell_pool).
:- mode dead_cell_pool_leave_scope(in, in, out) is det.

:- pred dead_cell_pool_try_to_reuse(int, dead_cell_pool, 
		set(reuse_var)).
:- mode dead_cell_pool_try_to_reuse(in, in, out) is det.

dead_cell_pool_init(HVS, Pool):- 
	map__init(Map),
	Pool = pool(HVS, Map).
dead_cell_pool_is_empty(pool(_, Pool)):- 
	map__is_empty(Pool).

add_dead_cell(ModuleInfo, ProcInfo, Var, Size, LFU, LBU, 
			Alias0, Pool0, Pool, Condition) :- 
	Pool0 = pool(HVS, _Map0), 
	reuse_condition_init(ModuleInfo, ProcInfo, Var, LFU, LBU, 
			Alias0, HVS, Condition),

		% XXX This needs to be investigated more, but cells of
		% size 0 are things like characters and integers and so
		% forth which aren't represented on the heap, so we
		% don't want to reuse their storage, I think.
	( Size > 0 ->
		add_dead_cell(Var, Size, Condition, Pool0, Pool)
	;
		Pool = Pool0
	).


add_dead_cell(Var, Size, ReuseCond, pool(HVS, Pool0), 
				     pool(HVS, Pool)) :- 
		% XXX Candidates are always zero. For the
		% moment we will not try to track this ! 
	Extra = extra(Size, ReuseCond, []),
	(
		map__insert(Pool0, Var, Extra, Pool1)
	->
		Pool = Pool1
	;
		error("(sr_dead) add_dead_cell: trying to add dead variable whilst already being marked as dead?")
	).


dead_cell_pool_least_upper_bound_disj(Vars, Pools, Pool):- 
	list__map(
		dead_cell_pool_leave_scope(Vars),
		Pools, 
		CleanedPools),
	(
		CleanedPools = [ C1 | _CR ]
	->
		Pool0 = C1,
		list__foldl(
			dead_cell_pool_least_upper_bound,
			CleanedPools, 
			Pool0, 
			Pool)
	;
		require__error("(sr_direct) dead_cell_pool_least_upper_bound_disj: trying to compute a lub_list of an empty list")
	).

dead_cell_pool_least_upper_bound(Pool1, Pool2, Pool) :- 
	Pool1 = pool(HVS, Map1), 
	map__init(Map0), 
	Pool0 = pool(HVS, Map0),
	map__foldl(
		dead_cell_pool_merge_var(Pool2),
		Map1, 
		Pool0,
		Pool).

:- pred dead_cell_pool_merge_var(dead_cell_pool, prog_var, 
			dead_extra_info, 
			dead_cell_pool, dead_cell_pool).
:- mode dead_cell_pool_merge_var(in, in, in, in, out) is det.

dead_cell_pool_merge_var(P2, Key1, Extra1, P0, P) :- 
	P2 = pool(_, Pool2),
	P0 = pool(HVS, Pool0),
	(
		map__search(Pool2, Key1, Extra2)
	->
		Extra1 = extra(A1, R1, _Cands1), 
		Extra2 = extra(A2, R2, _Cands2),
		int__min(A1, A2, A), 
		reuse_condition_merge(R1, R2, R),
			% XXX candidates not tracked
		Extra = extra(A, R, []),
		(
			map__insert(Pool0, Key1, Extra, Pool01)
		->
			P = pool(HVS, Pool01)
		;
			require__error("(sr_direct) dead_cell_pool_merge_var: trying to add already existing key to pool")
		)
	;	
		P = P0
	).

dead_cell_pool_leave_scope(ScopeVarsSet, P0, P) :- 
	P0 = pool(HVS, Pool0),
	set__to_sorted_list(ScopeVarsSet, ScopeVars),
	map__to_assoc_list(Pool0, AssocList0),
	list__filter(
		pred(Key::in) is semidet :- 
			(
				Key = ProgVar - _Extra,
				list__member(ProgVar, ScopeVars)
			),
		AssocList0,
		AssocList),
	map__from_assoc_list(AssocList, Pool),
	P = pool(HVS, Pool).
	
dead_cell_pool_try_to_reuse(Size, Pool, Set) :-
	Pool = pool(_HVS, Map), 
	map__to_assoc_list(Map, AssocList),
	list__filter(cons_can_reuse(Size), AssocList, CellsThatCanBeReused),
	list__map(to_pair_var_condition, 
			CellsThatCanBeReused, VarConditionPairs),
	set__list_to_set(VarConditionPairs, Set).

:- pred cons_can_reuse(int, pair(prog_var, dead_extra_info)).
:- mode cons_can_reuse(in, in) is semidet.

cons_can_reuse(Size, _Var - Extra) :- 
	Extra = extra(DeadSize, _, _), 
	Size =< DeadSize.

:- pred to_pair_var_condition(pair(prog_var, dead_extra_info), reuse_var).
:- mode to_pair_var_condition(in, out) is det.

to_pair_var_condition(Var - Extra, reuse_var(Var, Condition, no, no)) :- 
	Extra = extra(_, Condition, _).
