%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_alias: Manipulation of the type "alias", an intermediate 
% 	form for representing one single alias as a pair of 
%	datastructures. 
% main author: nancy

:- module possible_alias__pa_alias.

:- interface.

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module parse_tree__prog_data.
:- import_module structure_reuse__sr_live. % XXX should be removed, eventually.

:- import_module set, list.

%-------------------------------------------------------------------%
%-- exported types

% :- type alias.
% :- type alias == pair(datastruct).

%-------------------------------------------------------------------%
%-- exported predicates

	% Given a unification, extract the aliases it creates. 
	% Assignmenents between primitive types do not lead to new
	% aliases. 
	% XXX TO-DO: make certain that no aliases between primitive 
	% types are created, even for constructions and deconstructions.
:- pred from_unification(module_info::in, proc_info::in, 
		hlds_goal__unification::in, hlds_goal__hlds_goal_info::in, 
		list(alias)::out) is det.

:- pred live_from_in_use(set(prog_var)::in, list(alias)::in, 
		live_set::out) is det.

:- pred live_from_live0(module_info::in, proc_info::in, 
		live_set::in, list(alias)::in, live_set::out) is det.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
:- implementation.

:- import_module check_hlds__type_util.
:- import_module hlds__hlds_data.
:- import_module hlds__hlds_llds.
:- import_module parse_tree__mercury_to_mercury.
:- import_module parse_tree__prog_io_pasr.
:- import_module possible_alias__pa_datastruct.
:- import_module possible_alias__pa_selector.

:- import_module varset, require, int, map, std_util, string.

%-------------------------------------------------------------------%
% parsing routines
%-------------------------------------------------------------------%

	% contains_one_of_vars(SET, ALIAS, DATA)
	% returns true if ALIAS = DATA1 - DATA, 
	%	where DATA1 \in SET
	% 	  and DATA  \not\in SET

:- pred contains_one_of_vars(set(prog_var), alias, datastruct).
:- mode contains_one_of_vars(in, in, out) is semidet.

contains_one_of_vars(Set, Alias, DATA) :- 
	Alias = Data1 - Data2,
	Var1 = Data1^sc_var,
	Var2 = Data2^sc_var,
	(
		set__member(Var1, Set)
	->
		not(set__member(Var2, Set)),
		DATA = Data2
	;
		set__member(Var2, Set) 
	->
		not(set__member(Var1, Set)),
		DATA = Data1
	;
		fail
	).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred number_args(list(prog_var)::in, 
		list(pair(int, prog_var))::out) is det.
number_args(Args, NumberedArgs) :- 
	list__map_foldl(
		pred(A::in, AP::out, Nin::in, Nout::out) is det:- 
		(
			AP = std_util:'-'(Nin, A),
			Nout = Nin + 1
		),
		Args,
		NumberedArgs,
		1, _).
	
from_unification(HLDS, ProcInfo, 
		construct(Var, Cons, Args0, _, _, _, _), _Info, AS) :-
	get_rid_of_damn_typeinfos(Cons, Args0, Args),
	number_args(Args, NumberedArgs), 
	list__foldl(alias_from_unif(HLDS, ProcInfo, Var, Cons), 
						NumberedArgs, [], AS0), 
	internal_aliases(NumberedArgs, PosList), 
	create_internal_aliases(Var, Cons, PosList, AS1), 
	list__append(AS0, AS1, AS). 
	

	% Given a list of arguments of the construction, determine all
	% the sets of positions which refer to the same prog_var. 
:- pred internal_aliases(list(pair(int, prog_var))::in, 
		list(list(int))::out) is det.
internal_aliases(NumberedArgs, PosList):- 
	list__foldl(
		pred(NumberedArg::in, Map0::in, Map::out) is det:- 
		    (
			NumberedArg = Position - ProgVar, 
			(
				map__search(Map0, ProgVar, Positions0)
			->
				Positions = [Position | Positions0],
				map__det_update(Map0, ProgVar, Positions, Map)
			;
				map__det_insert(Map0, ProgVar, [Position], Map)
			)
		    ),
		NumberedArgs, 
		map__init, 
		FrequencyMap0),
	map__keys(FrequencyMap0, Keys), 
	list__foldl(
		pred(ProgVar::in, List0::in, List::out) is det :- 
		    (
			map__lookup(FrequencyMap0, ProgVar, Positions),
			(
				(Positions = [] ; Positions = [_])
			-> 
				List = List0
			; 	
				List = [Positions | List0]
			)
		   ), 
		Keys, 
		[],
		PosList). 

:- pred create_internal_aliases(prog_var::in, cons_id::in, 
		list(list(int))::in, list(alias)::out) is det. 
create_internal_aliases(MainVar, ConsId, PositionLists, Aliases):- 
	list__foldl(
		pred(Positions::in, List0::in, List::out) is det:-
		    (
			solutions_set(two_by_two(Positions), SetPairs), 
			set__to_sorted_list(SetPairs, Pairs),
			list__append(Pairs, List0, List)
		   ), 
		PositionLists, 
		[], 
		PositionPairs), 
	list__map(
		pred(PositionPair::in, Alias::out) is det:-
		    (
			PositionPair = Pos0 - Pos1,
			pa_datastruct__init(MainVar, ConsId, Pos0, D0), 
			pa_datastruct__init(MainVar, ConsId, Pos1, D1), 
			Alias = D0 - D1
		    ), 
		PositionPairs, 
		Aliases). 
			
:- pred two_by_two(list(int)::in, pair(int)::out) is nondet. 
two_by_two(List0, Pair):-
	(
		List0 = []
	->
		require__error("empty list")
	; 
		list__delete(List0, E0, Rest0), 
		list__delete(Rest0, E1, _), 
		(
			E0 > E1
		-> 
			Pair = E1 - E0
		; 
			Pair = E0 - E1 
		)
	). 
			
:- pred get_rid_of_damn_typeinfos(cons_id::in, list(prog_var)::in, 
		list(prog_var)::out) is det. 
get_rid_of_damn_typeinfos(Cons, Args0, Args) :- 
	cons_id_maybe_arity(Cons, MaybeArity), 
	(
		MaybeArity = yes(RealArity)
	-> 
		list__length(Args0, PseudoArity),
		(
			RealArity = PseudoArity
		-> 
			Args = Args0
		;
			Diff = PseudoArity - RealArity,
			(
				list__drop(Diff, Args0, Args1)
			->
				Args = Args1
			; 	
				require__error("Blabla")
			)
		)	
	;
		Args = Args0
	).
	

from_unification(HLDS, ProcInfo, 
		deconstruct(Var, Cons, Args0, _, _, _), Info, AS) :-
	get_rid_of_damn_typeinfos(Cons, Args0, Args), 
	number_args(Args, NumberedArgs),
	optimize_for_deconstruct(NumberedArgs, Info, ReducedArgs),
	list__foldl(alias_from_unif(HLDS, ProcInfo, Var, Cons), 
			ReducedArgs, [], AS).

:- pred optimize_for_deconstruct(list(pair(int, prog_var))::in, 
		hlds_goal_info::in, list(pair(int, prog_var))::out) is det.
	% For deconstructions, a huge optimization can be made by
	% avoiding the construction of aliases involving variables 
	% which are not used anyway.
optimize_for_deconstruct(Args, Info, ReducedArgs) :- 
	% Of all the args of a deconstruct, only the ones that are
	% in the pre-birth set are actually used during the subsequent
	% part of the code. Therefore, instead of creating aliases
	% between the deconstructed var and all the args of the
	% deconstruction, it is enough to consider only those with 
	% the args which are in pre-birth. 
	hlds_llds__goal_info_get_pre_births(Info, PreB),
	keep_only_the_prebirths_v2(PreB, Args, ReducedArgs).

:- pred keep_only_the_prebirths_v2(set(prog_var)::in, 
		list(pair(int, prog_var))::in,
		list(pair(int, prog_var))::out) is det.

keep_only_the_prebirths_v2(PreB, AllArgs, RES) :- 
	set__to_sorted_list(PreB, ListPreB), 
	keep_only_the_prebirths_v2_2(ListPreB, AllArgs, [], RES).

:- pred keep_only_the_prebirths_v2_2(list(prog_var)::in, 
		list(pair(int, prog_var))::in,
		list(pair(int, prog_var))::in,
		list(pair(int, prog_var))::out) is det.
keep_only_the_prebirths_v2_2(PreB, AllArgs, ACC, RES):-
	(
		PreB = [ X | Xs ]
	->
		(
			list_find(X, Arg, AllArgs, AllArgs0)
		-> 
			ACC0 = [ Arg | ACC ],
			AllArgs1 = AllArgs0
		; 
			ACC0 = ACC,
			AllArgs1 = AllArgs
		), 
		keep_only_the_prebirths_v2_2(Xs, AllArgs1, ACC0, RES)
	;
		RES = ACC
	).

:- pred list_find(prog_var::in, pair(int, prog_var)::out, 
		list(pair(int, prog_var))::in, 
		list(pair(int, prog_var))::out) is semidet.

list_find(Var, Arg, Lin, Lout) :-
	Lin = [ First | Rest ],
	(
		First = std_util:'-'(_, Var)
	->
		Arg = First,
		Lout = Rest
	;
		list_find(Var, Arg, Rest, Tmp), 
		Lout = [ First | Tmp ]
	).
			

from_unification(HLDS, ProcInfo, assign(Var1,Var2), _, AS):-
	(
		is_of_a_primitive_type(ProcInfo, HLDS, Var1)
	->
		AS = []
	;
		pa_datastruct__init(Var1,D1),
		pa_datastruct__init(Var2,D2),
		Alias = D1 - D2,
		AS = [Alias]
	).

from_unification(_HLDS, _ProcInfo, simple_test(_A,_B), _, AS):-
	AS = [].

from_unification(_HLDS, _ProcInfo, complicated_unify(_,_,_), _, AS):-
	% XXX only if partially instantiated datastructures cannot
	% exist.
	AS = [].

:- pred is_of_a_primitive_type(proc_info::in, module_info::in, 
		prog_var::in) is semidet.
is_of_a_primitive_type(ProcInfo, HLDS, Var):-
	proc_info_vartypes(ProcInfo, VarTypes),
	map__lookup(VarTypes, Var, VarType), 
	type_util__type_is_atomic(VarType, HLDS).

:- pred alias_from_unif(module_info::in, proc_info::in, 
		prog_var::in, cons_id::in, pair(int, prog_var)::in, 
		list(alias)::in, list(alias)::out) is det.
alias_from_unif(ModuleInfo, ProcInfo, Var, Cons, N - ARG, List0, List):-
	(
		is_of_a_primitive_type(ProcInfo, ModuleInfo, ARG)
	-> 
		List = List0
	; 
		pa_datastruct__init(Var, Cons, N, D1),
		pa_datastruct__init(ARG, D2),
		Alias = D1 - D2,
		List = [Alias | List0]
	).

	% switch the order of the alias...
:- pred switch(alias::in, alias::out) is det.
switch(D1 - D2, D2 - D1).
	
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

live_from_in_use(InUse, Aliases, Live):-
	% filter the list of aliases, keeping only the ones that 
	% involve at least one variable from the IN_USE set
	list__filter_map(
		pa_alias__contains_one_of_vars(InUse),
		Aliases,
		Datastructs),
	sr_live__from_datastructs(Datastructs, Live).

live_from_live0(ModuleInfo, ProcInfo, Live0, Aliases, Live):- 
	(
		(sr_live__top(Live0) ; sr_live__bottom(Live0))
	->
		Live = Live0
	;
		sr_live__get_datastructs(Live0, Datastructs0),
		list__map(
			pa_alias__one_of_vars_is_live(ModuleInfo,
				ProcInfo, Datastructs0),
			Aliases,
			DatastructsLists), 
		list__condense(DatastructsLists, Datastructs),
		sr_live__from_datastructs(Datastructs, Live)
	).

	% one_of_vars_is_live(LIST, ALIAS, X^sx1)
	% returns true if
	% 	ALIAS = X^sx - Y^sy
	%   and Y^s1 \in LIST and
	%		sy = s1.s2 => sx1 = sx
	% 	   or
	%		sy.s2 = s1 => sx1 = sx.s2
:- pred one_of_vars_is_live(module_info::in, proc_info::in, 
		list(prog_data__datastruct)::in, alias::in, 
		list(prog_data__datastruct)::out) is det.
one_of_vars_is_live(ModuleInfo, ProcInfo, Datastructs0, 
		Alias0, Datastructs) :- 
	one_of_vars_is_live_ordered(ModuleInfo, ProcInfo, 
		Datastructs0, Alias0, L1), 
	switch(Alias0, AliasSW),	
	one_of_vars_is_live_ordered(ModuleInfo, ProcInfo, 
		Datastructs0, AliasSW, L2),
	list__append(L1,L2, Datastructs).

:- pred one_of_vars_is_live_ordered(module_info::in, proc_info::in,
		list(prog_data__datastruct)::in, alias::in,
		list(prog_data__datastruct)::out) is det.
one_of_vars_is_live_ordered(ModuleInfo, ProcInfo, List, ALIAS, List_Xsx1) :- 
	ALIAS = Xsx - Ysy,
	list__filter(same_vars(Ysy), List, Y_List),
	(
		% first try to find one of the found datastructs which is 
		% fully alive: so that Ysy is less or equal to at least one
		% Ys1 in Y_List (sy = s1.s2)
		list__filter(
			pred(Ys1::in) is semidet :-
			    (pa_datastruct__less_or_equal(ModuleInfo, 
					ProcInfo, Ysy, Ys1, _s2)),
			Y_List,
			FY_List),
		FY_List = [_|_]
	->
		Xsx1 = Xsx,
		List_Xsx1 = [Xsx1]
	;
		% find all datastructs from Y_List which are less or 
		% equal to Ysy, select the one with the shortest selector
		% (note that there should be only one solution. if more
		% than one such datastruct is found, the initial live_set
		% is not minimal, while this should be somehow guaranteed).
		list__filter_map(
			pred(Ys1::in, S2::out) is semidet :-
			    (pa_datastruct__less_or_equal(ModuleInfo, 
					ProcInfo, Ysy, Ys1, S2)),
			Y_List,
			SelectorList),
		% each sx1 = sx.s2, where s2 is one of SelectorList
		list__map(
			pred(S2::in, Xsx1::out) is det :-
			    (pa_datastruct__termshift(Xsx, S2, Xsx1)),
			SelectorList,
			List_Xsx1)
	).
			
