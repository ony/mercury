%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_choice
% Main authors: petdr
% 
% Given a goal annotated with information about which cells are
% canditates for reuse and a strategy determine which cells will
% actually be reused and the conditions that reuse implies on the head
% variables.
%
%-----------------------------------------------------------------------------%

:- module sr_choice.
:- interface.

:- import_module hlds_goal, sr_data.
:- import_module list, std_util.

:- type strategy
	--->	strategy(
			constraint,
			selection
		).

	% The constraint on the cells that we consider available for
	% reuse.
:- type constraint
	--->	same_cons_id
	;	within_n_cells_difference(int)
	.

	% After the constraint has been applied to the set of cells
	% which are available for reuse, determine which of that set we
	% select.
:- type selection
	--->	lifo
	;	random
	.

:- pred sr_choice__process_goal(strategy::in, hlds_goal::in, hlds_goal::out,
		maybe(list(reuse_condition))::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module hlds_data, prog_data.
:- import_module assoc_list, int, multi_map, require, set.

process_goal(Strategy, Goal0, Goal, MaybeReuseConditions) :-
	Strategy = strategy(Constraint, SelectionRule),
	apply_constraint(Constraint, Goal0, Goal1),
	select_reuses(SelectionRule, Goal1, Goal, ReuseConditions),
	( ReuseConditions = [] ->
		MaybeReuseConditions = no
	;
		MaybeReuseConditions = yes(ReuseConditions)
	).
	
%-----------------------------------------------------------------------------%

:- type constraint_info
	--->	constraint_info(
			map	:: multi_map(prog_var, cons_id)
		).

:- pred constraint_info_init(constraint_info::out) is det.

constraint_info_init(constraint_info(Map)) :-
	multi_map__init(Map).

:- pred apply_constraint(constraint::in, hlds_goal::in, hlds_goal::out) is det.

apply_constraint(Constraint, Goal0, Goal) :-
	constraint_info_init(ConstraintInfo),
	apply_constraint(Constraint, Goal0, Goal, ConstraintInfo, _).

:- pred apply_constraint(constraint::in, hlds_goal::in, hlds_goal::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint(_Constraint, Goal - GoalInfo, Goal - GoalInfo) -->
	{ Goal = call(_PredId, _ProcId, _Args, _Builtin, _MaybeCtxt, _Name) }.

apply_constraint(Constraint, Goal - GoalInfo0, Goal - GoalInfo) -->
	{ Goal = unify(_Var, _Rhs, _Mode, Unification, _Ctxt) },
	apply_constraint_unification(Constraint, Unification, GoalInfo0, GoalInfo).

apply_constraint(_Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = generic_call(_, _, _, _) },
	{ Goal = Goal0 }.
apply_constraint(_Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = pragma_foreign_code(_, _, _, _, _, _, _, _) },
	{ Goal = Goal0 }.
apply_constraint(_Constraint, Goal0 - _GoalInfo, _) -->
	{ Goal0 = bi_implication(_, _) },
	{ error("structure_reuse: bi_implication.\n") }.

apply_constraint(Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = if_then_else(Vars, If0, Then0, Else0, SM) },
	apply_constraint(Constraint, If0, If),
	=(IfInfo),
	{ apply_constraint(Constraint, Then0, Then, IfInfo, ThenInfo) },
	{ apply_constraint(Constraint, Else0, Else, IfInfo, ElseInfo) },
	merge(ThenInfo),
	merge(ElseInfo),
	{ Goal = if_then_else(Vars, If, Then, Else, SM) }.

apply_constraint(Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = switch(Var, CanFail, Cases0, StoreMap) },
	=(InitSwitchInfo),
	apply_constraint_cases(Constraint, InitSwitchInfo, Cases0, Cases),
	{ Goal = switch(Var, CanFail, Cases, StoreMap) }.

apply_constraint(Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = some(Vars, CanRemove, SomeGoal0) },
	apply_constraint(Constraint, SomeGoal0, SomeGoal),
	{ Goal = some(Vars, CanRemove, SomeGoal) }.

apply_constraint(Constraint, not(Goal0) - GoalInfo, not(Goal) - GoalInfo) -->
	apply_constraint(Constraint, Goal0, Goal).

apply_constraint(Constraint, conj(Goal0s) - GoalInfo,
		conj(Goals) - GoalInfo) -->
	apply_constraint_list(Constraint, Goal0s, Goals).

apply_constraint(Constraint, disj(Goal0s, SM) - GoalInfo,
		disj(Goals, SM) - GoalInfo) -->
	=(InitDisjInfo),
	apply_constraint_disj(Constraint, InitDisjInfo, Goal0s, Goals).

apply_constraint(Constraint, par_conj(Goal0s, SM) - GoalInfo,
		par_conj(Goals, SM) - GoalInfo) -->
	apply_constraint_list(Constraint, Goal0s, Goals).

:- pred apply_constraint_cases(constraint::in, constraint_info::in,
		list(case)::in, list(case)::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_cases(_Constraint, _Info0, [], []) --> [].
apply_constraint_cases(Constraint, Info0, [Case0 | Case0s], [Case | Cases]) -->
	{ Case0 = case(ConsId, Goal0) },
	{ apply_constraint(Constraint, Goal0, Goal, Info0, Info) },
	merge(Info),
	{ Case = case(ConsId, Goal) },
	apply_constraint_cases(Constraint, Info0, Case0s, Cases).

:- pred apply_constraint_list(constraint::in, hlds_goals::in, hlds_goals::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_list(_Constraint, [], []) --> [].
apply_constraint_list(Constraint, [Goal0 | Goal0s], [Goal | Goals]) -->
	apply_constraint(Constraint, Goal0, Goal),
	apply_constraint_list(Constraint, Goal0s, Goals).

:- pred apply_constraint_disj(constraint::in,
		constraint_info::in, hlds_goals::in, hlds_goals::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_disj(_Constraint, _Info0, [], []) --> [].
apply_constraint_disj(Constraint, Info0, [Goal0 | Goal0s], [Goal | Goals]) -->
	{ apply_constraint(Constraint, Goal0, Goal, Info0, Info) },
	merge(Info),
	apply_constraint_disj(Constraint, Info0, Goal0s, Goals).

:- pred merge(constraint_info::in, constraint_info::in,
		constraint_info::out) is det.

merge(InfoA, Info0, Info) :-
	multi_map__merge(InfoA ^ map, Info0 ^ map, Map),
	Info = Info0 ^ map := Map.

:- pred apply_constraint_unification(constraint::in, unification::in,
		hlds_goal_info::in, hlds_goal_info::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_unification(Constraint, Unif, GoalInfo0, GoalInfo) -->
	{ Unif = construct(_Var, ConsId, _Vars, _Ms, _HTC, _IsUniq, _Aditi) },
	{ goal_info_get_reuse(GoalInfo0, ReuseInfo) },
	{ ReuseInfo = choice(construct(Pairs)) ->
		PossibleCandidates = set__to_sorted_list(Pairs)
	;
		error("sr_choice__apply_constraint_unification")
	},
	Map =^ map,
	(
		{ Constraint = same_cons_id },

			% XXX recode this more efficiently at some stage.
		{ P = (pred(Candidate::out) is nondet :- 
			list__member(Candidate, PossibleCandidates),
			CandidateVar = fst(Candidate),
			multi_map__search(Map, CandidateVar, [ConsId])
		)}
	;
		{ Constraint = within_n_cells_difference(Difference) },

			% XXX Are two cells with the same arity the same
			% size?  I think not, because the cell may
			% contain existentially typed compenents which
			% require storage of the corresponding type
			% infos.
		{ P = (pred(Candidate::out) is nondet :- 
			list__member(Candidate, PossibleCandidates),
			CandidateVar = fst(Candidate),
			multi_map__search(Map, CandidateVar, ConsIds),
			cons_id_arity(ConsId, Arity),
			all [ReuseConsId] (
				list__member(ReuseConsId, ConsIds)
			=>
				(
					cons_id_arity(ReuseConsId, ReuseArity),
					ReuseArity - Arity =< Difference
				)
			)
		)}
	),
	{ solutions(P, Candidates) },
	{ goal_info_set_reuse(GoalInfo0,
			choice(construct(set__list_to_set(Candidates))),
			GoalInfo) }.

apply_constraint_unification(_Constraint, Unif, GoalInfo0, GoalInfo) -->
	{ Unif = deconstruct(Var, ConsId, _Vars, _Modes, _CanFail, _CanCGC) },

	{ goal_info_get_reuse(GoalInfo0, ReuseInfo) },
	{ ReuseInfo = choice(deconstruct(MaybeDies)) ->
		(
			MaybeDies = yes(_Condition),
			goal_info_set_reuse(GoalInfo0, reuse(cell_died),
					GoalInfo)
		;
			MaybeDies = no,
			goal_info_set_reuse(GoalInfo0, reuse(no_reuse),
					GoalInfo)
		)
	;
		error("sr_choice__apply_constraint_unification")
	},

	Map0 =^ map,
	{ multi_map__set(Map0, Var, ConsId, Map) },
	^ map := Map.
apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = assign(_, _) }.
apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = simple_test(_, _) }.
apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = complicated_unify(_, _, _) }.


%-----------------------------------------------------------------------------%

:- import_module queue.

:- type selection_info
	--->	selection_info(
			local_used	:: set(prog_var),
			global_used	:: set(prog_var),
			reuse_conds	:: list(reuse_condition),
		
			lifo		:: lifo
		).

:- type lifo
	--->	lifo(
			all_locals	:: list(list(prog_var)),
			local		:: list(prog_var),
			global		:: list(list(prog_var))
		).

:- func selection_info_init = selection_info.

selection_info_init = selection_info(set__init, set__init, [], lifo([],[],[])).

:- pred select_reuses(selection::in, hlds_goal::in, hlds_goal::out,
		list(reuse_condition)::out) is det.

select_reuses(SelectionRule, Goal0, Goal, ReuseConditions) :-
	select_reuses(SelectionRule, Goal0, Goal, selection_info_init, Info),
	ReuseConditions = Info ^ reuse_conds.

:- pred select_reuses(selection::in, hlds_goal::in, hlds_goal::out,
		selection_info::in, selection_info::out) is det.

select_reuses(_Selection, Goal - GoalInfo, Goal - GoalInfo) -->
	{ Goal = call(_PredId, _ProcId, _Args, _Builtin, _MaybeCtxt, _Name) }.

select_reuses(Selection, Goal - GoalInfo0, Goal - GoalInfo) -->
	{ Goal = unify(_Var, _Rhs, _Mode, Unification, _Ctxt) },
	select_reuses_unification(Selection, Unification, GoalInfo0, GoalInfo).

select_reuses(_Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = generic_call(_, _, _, _) },
	{ Goal = Goal0 }.
select_reuses(_Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = pragma_foreign_code(_, _, _, _, _, _, _, _) },
	{ Goal = Goal0 }.
select_reuses(_Selection, Goal0 - _GoalInfo, _) -->
	{ Goal0 = bi_implication(_, _) },
	{ error("structure_reuse: bi_implication.\n") }.

select_reuses(Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = if_then_else(Vars, If0, Then0, Else0, SM) },
	select_reuses(Selection, If0, If),
	selection_start_branch,
	=(IfInfo),
	{ select_reuses(Selection, Then0, Then, IfInfo, ThenInfo) },
	{ select_reuses(Selection, Else0, Else, IfInfo, ElseInfo) },
	selection_merge(ThenInfo),
	selection_merge(ElseInfo),
	selection_end_branch,
	{ Goal = if_then_else(Vars, If, Then, Else, SM) }.

select_reuses(Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = switch(Var, CanFail, Cases0, StoreMap) },
	selection_start_branch,
	=(InitSwitchInfo),
	select_reuses_cases(Selection, InitSwitchInfo, Cases0, Cases),
	{ Goal = switch(Var, CanFail, Cases, StoreMap) }.

select_reuses(Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = some(Vars, CanRemove, SomeGoal0) },
	select_reuses(Selection, SomeGoal0, SomeGoal),
	{ Goal = some(Vars, CanRemove, SomeGoal) }.

select_reuses(Selection, not(Goal0) - GoalInfo, not(Goal) - GoalInfo) -->
	select_reuses(Selection, Goal0, Goal).

select_reuses(Selection, conj(Goal0s) - GoalInfo,
		conj(Goals) - GoalInfo) -->
	select_reuses_list(Selection, Goal0s, Goals).

select_reuses(Selection, disj(Goal0s, SM) - GoalInfo,
		disj(Goals, SM) - GoalInfo) -->
	selection_start_branch,
	=(InitDisjInfo),
	select_reuses_disj(Selection, InitDisjInfo, Goal0s, Goals).

select_reuses(Selection, par_conj(Goal0s, SM) - GoalInfo,
		par_conj(Goals, SM) - GoalInfo) -->
	select_reuses_list(Selection, Goal0s, Goals).

:- pred select_reuses_cases(selection::in, selection_info::in,
		list(case)::in, list(case)::out,
		selection_info::in, selection_info::out) is det.

select_reuses_cases(_Selection, _Info0, [], []) --> selection_end_branch.
select_reuses_cases(Selection, Info0, [Case0 | Case0s], [Case | Cases]) -->
	{ Case0 = case(ConsId, Goal0) },
	{ select_reuses(Selection, Goal0, Goal, Info0, Info) },
	selection_merge(Info),
	{ Case = case(ConsId, Goal) },
	select_reuses_cases(Selection, Info0, Case0s, Cases).

:- pred select_reuses_list(selection::in, hlds_goals::in, hlds_goals::out,
		selection_info::in, selection_info::out) is det.

select_reuses_list(_Selection, [], []) --> [].
select_reuses_list(Selection, [Goal0 | Goal0s], [Goal | Goals]) -->
	select_reuses(Selection, Goal0, Goal),
	select_reuses_list(Selection, Goal0s, Goals).

:- pred select_reuses_disj(selection::in,
		selection_info::in, hlds_goals::in, hlds_goals::out,
		selection_info::in, selection_info::out) is det.

select_reuses_disj(_Selection, _Info0, [], []) --> selection_end_branch.
select_reuses_disj(Selection, Info0, [Goal0 | Goal0s], [Goal | Goals]) -->
	{ select_reuses(Selection, Goal0, Goal, Info0, Info) },
	selection_merge(Info),
	select_reuses_disj(Selection, Info0, Goal0s, Goals).

	%
	% This merges in the select_info left after the end of each
	% branch with the global one.
	%
:- pred selection_merge(selection_info::in, selection_info::in,
		selection_info::out) is det.

selection_merge(selection_info(LocalA, GlobalA, CondsA, LifoA),
		selection_info(LocalB, GlobalB, CondsB, LifoB),
		selection_info(Local, Global, Conds, Lifo)) :-
	Local = LocalA `set__union` LocalB,
	Global = GlobalA `set__union` GlobalB,
	Conds = CondsA ++ CondsB,

	LifoA = lifo(AllLocalsA, LocalsA, GlobalsA),
	LifoB = lifo(AllLocalsB, LocalsB, GlobalsB),
	Lifo  = lifo([LocalsA | AllLocalsB], [], GlobalsB),

	require(unify(LocalsB, []),
			"selection_merge: LocalsB not empty"),
	require(unify(AllLocalsA, []),
			"selection_merge: AllLocalsA not equal"),
	require(unify(GlobalsA, GlobalsB),
			"selection_merge: Globals not equal").
	 

	%
	% At the start of processing all branches of a 
	% disj/switch/if_then_else this predicate should be called.
	%
:- pred selection_start_branch(selection_info::in, selection_info::out) is det.

selection_start_branch(selection_info(Local0, Global0, Conds0, Lifo0),
		selection_info(Local, Global, Conds, Lifo)) :-
	Local = set__init,
	Global = Local0 `set__union` Global0,
	Conds = Conds0,

	Lifo0 = lifo(AllLocals, Locals, Globals),
	Lifo  = lifo(AllLocals, [], [Locals | Globals]).

	%
	% At the end of processing all branches of a
	% disj/switch/if_then_else this predicate should be called.
	%
:- pred selection_end_branch(selection_info::in, selection_info::out) is det.

selection_end_branch(selection_info(Local0, Global0, Conds0, Lifo0),
		selection_info(Local, Global, Conds, Lifo)) :-
	Local = set__init,
	Global = Local0 `set__union` Global0,
	Conds = Conds0,

	Lifo0 = lifo(AllLocals0, Locals0, Globals0),
	( Globals0 = [G | Gs] ->
		Locals = list_merge([Locals0 | AllLocals0]) ++ G,
		Globals = Gs
	;
		Locals = list_merge([Locals0 | AllLocals0]),
		Globals = []
	),
	Lifo  = lifo([], Locals, Globals).

	% [ [1a,2a], [2b,1b], [2c,3c,1c] ] -> [1a, 2b, 2c, 2a, 1b, 3c, 1c]
:- func list_merge(list(list(T))) = list(T).

list_merge(List) = Result :-
	list_merge(List, Tail, Head),
	(  Tail = [] ->
		Result = list__reverse(Head)
	;
		Result = Head ++ list_merge(Tail)
	).


:- pred list_merge(list(list(T))::in, list(list(T))::out, list(T)::out) is det.

list_merge([], [], []).
list_merge([H | T], Tail, Head) :-
	(
		H = [],
		list_merge(T, Tail, Head)
	;
		H = [X | Xs],
		list_merge(T, Tail0, Head0),
		Tail = [Xs | Tail0],
		Head = [X | Head0]
	).

:- pred select_reuses_unification(selection::in, unification::in,
		hlds_goal_info::in, hlds_goal_info::out,
		selection_info::in, selection_info::out) is det.

select_reuses_unification(Selection, Unif, GoalInfo0, GoalInfo) -->
	{ Unif = construct(_Var, _ConsId, _Vars, _Ms, _HTC, _IsUniq, _Aditi) },
	{ goal_info_get_reuse(GoalInfo0, ReuseInfo) },
	{ ReuseInfo = choice(construct(Pairs)) ->
		PossibleCandidates = set__to_sorted_list(Pairs)
	;
		error("sr_choice__apply_selection_unification")
	},

	LocalReused0 =^ local_used,
	GlobalReused =^ global_used,

	(
		{ Selection = lifo },
		Locals =^ lifo ^ local,
		Globals =^ lifo ^ global,
		{ F = (pred(Var::in, Var - Cond::out) is semidet :-
				assoc_list__search(PossibleCandidates,
						Var, Cond),
				\+ set__member(Var, LocalReused0),
				\+ set__member(Var, GlobalReused)
			)},
		{ list__filter_map(F,
				Locals ++ list__condense(Globals), Candidates) }
	;
		{ Selection = random },
		{ P = (pred(Choice::out) is nondet :- 
			list__member(Choice, PossibleCandidates),
			ChoiceVar = fst(Choice),
			\+ set__member(ChoiceVar, LocalReused0),
			\+ set__member(ChoiceVar, GlobalReused)
		)},

		{ solutions(P, Candidates) }
	),
	( { Candidates = [ReuseVar - ReuseCond | _] } ->
		{ set__insert(LocalReused0, ReuseVar, LocalReused) },
		{ goal_info_set_reuse(GoalInfo0,
				reuse(cell_reused(ReuseVar)),
				GoalInfo) },
		ReuseConditions =^ reuse_conds,
		^ reuse_conds := [ReuseCond | ReuseConditions]
	;
		{ LocalReused = LocalReused0 },
		{ goal_info_set_reuse(GoalInfo0,
				reuse(no_reuse),
				GoalInfo) }
	),
	^ local_used := LocalReused.

select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = deconstruct(Var, _ConsId, _Vars, _Modes, _CanFail, _CanCGC) },
	Locals0 =^ lifo ^ local,
	^ lifo ^ local := [Var | Locals0].

select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = assign(_, _) }.
select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = simple_test(_, _) }.
select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = complicated_unify(_, _, _) }.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
