%-----------------------------------------------------------------------------%
% Copyright (C) 2001-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_alias_set: defines the actual (hidden) representation for
% lists of aliased data structures.

% main author: nancy

% TO DO: 
% 	- record type of the selectorset immediately in the set. 

:- module possible_alias__pa_alias_as__pa_alias_set. 

:- interface.

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module parse_tree__prog_data. 
:- import_module possible_alias__pa_alias.
:- import_module possible_alias__pa_datastruct. 

:- import_module list, set, map, io, term, bool.

%-----------------------------------------------------------------------------%
:- type alias_set. 

:- pred init(alias_set::out) is det.
:- func init = alias_set is det. 
:- pred is_empty(alias_set::in) is semidet.
:- func size(alias_set) = int.

	% Conversion between list of aliases to alias_set's and vice versa.
:- pred from_pair_alias_list(list(alias)::in, alias_set::out) is det.
:- pred to_pair_alias_list(alias_set::in, list(alias)::out) is det.

	% Projection-operations. Given a list or set of prog_vars, 
	% keep only that part of the alias_set that relates to those
	% prog_vars. 
:- pred project(list(prog_var)::in, alias_set::in, alias_set::out) is det. 
:- pred project_set(set(prog_var)::in, alias_set::in, 
		alias_set::out) is det.

	% Compute all the datastructures that point to the same memory space
	% occupied by a given data structure. 
:- pred collect_aliases_of_datastruct(module_info::in, proc_info::in, 
		pa_datastruct__datastruct::in, alias_set::in,
		list(pa_datastruct__datastruct)::out) is det.

	% Rename the prog_vars occurring in the alias_set, using
	% a map that maps the to-be-replaced-vars with on the
	% new prog_vars. 
:- pred rename(map(prog_var,prog_var)::in, alias_set::in, 
		alias_set::out) is det. 
	
	% Rename the types occurring in the alias_set, applying
	% the given substitution to each of the types encountered. 
:- pred rename_types(term__substitution(tvar_type)::in, 
		alias_set::in, alias_set::out) is det.

	% Equality test. Needed for the fixpoint computation. 
:- pred equal(alias_set::in, alias_set::in) is semidet. 

	% Compute the least upper bound of alias_sets.
:- pred least_upper_bound(module_info::in, proc_info::in, 
		alias_set::in, alias_set::in, alias_set::out) is det.
:- pred least_upper_bound_list(module_info::in, proc_info::in, 
		list(alias_set)::in, alias_set::out) is det.

	% extend(ModuleInfo, ProcInfo, NewAliasSet, OldAliasSet, 
	%			ComputedAliasSet). 
	% Extend a given OldAliasSet with the information contained
	% in the NewAliasSet. Note that order here is very important!
	% The NewAliasSet is the alias_set that was computed for
	% one specific atom. This information needs to be computed
	% with the aliases that already existed at the program point
	% corresponding to this atom (the OldAliasSet). 
	% ==> alternating closure.
:- pred extend(module_info::in, proc_info::in, alias_set::in, 
		alias_set::in, alias_set::out) is det.

	% Add two alias_sets together without bothering to extend
	% one against the other. 
	% XXX What makes this operation so different from the
	% least_upper_bound? Check!
:- pred add(alias_set::in, alias_set::in, alias_set::out) is det.
	
	% Normalize all the selectors within the alias_set and
	% simplify if necessary. 
:- pred normalize(module_info::in, proc_info::in,  
		alias_set::in, alias_set::out) is det.

	% less_or_equal(ModuleInfo, ProcInfo, AliasSet1, AliasSet2). 
:- pred less_or_equal(module_info::in, proc_info::in, 
		alias_set::in, alias_set::in) is semidet.

	% Remove all the information regarding the given list of
	% variables. 
:- pred remove_vars(list(prog_var)::in, alias_set::in, 
		alias_set::out) is det. 

	% Apply widening. The integer represents a threshold.  If the size of
	% the set is larger than that threshold, widening is performed, in
	% which case the boolean is set to "true". 
:- pred apply_widening(module_info::in, proc_info::in, int::in, 
		alias_set::in, alias_set::out, bool::out) is det.

%----------------------------------------------------------------------------%
% printing predicates
%----------------------------------------------------------------------------%

	% print(PredInfo, ProcInfo, AliasSet, StartingString, EndString)
	% Prints each alias as a parsable pair of datastructs, each
	% alias preceded with the StartingString, and ended with the
	% EndString.
:- pred print(pred_info::in, proc_info::in, alias_set::in, 
		string::in, string::in, 
		io__state::di, io__state::uo) is det.

	% print(PredInfo, ProcInfo, AliasSet, StartingString,
	% MiddleString, EndString)
	% Prints each alias as a parsable pair of datastructs. Each alias
	% is preceded with a StartingString, and Ended with an EndString. 
	% Between aliases, the MiddleString is printed. 
:- pred print(pred_info::in, proc_info::in, alias_set::in, 
		string::in, string::in, string::in, 
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module possible_alias__pa_selector.

:- import_module std_util.
:- import_module int, bool, assoc_list. 
:- import_module require, string. 

%-----------------------------------------------------------------------------%
%-- type definitions

% Example of how the aliases are represented:
% 1. { (X^\epsilon - Y^\epsilon) } is represented as: 
% 	alias_set(2, 		% size is two (as every alias is counted twice)
% 	    { 
%		X -> 
%		   alias_sel_set(1,
%			{ \epsilon -> Y^\epsilon }
%			)
%		Y -> 
%		   alias_sel_set(1,
%			{ \epsilon -> X^\epsilon }
%			)
% 	    }
%	)
% 
% 

	% In the alias_set we keep a mapping of every prog_var to a
	% description of the aliases it is involved with. Each of these
	% aliases is represented by yet another mapping. This time the
	% mapping maps selectors on a data set. If (Sel-Data) is in the
	% mapping for a variable V, then this means that V^Sel is aliased with
	% each of the data structures kept in Data.
	% We explicitly keep track of the size of the alias_set. 
:- type alias_set ---> 
		alias_set(
			int, 		% total number of aliases 
						% represented by this set.
%			set(prog_var), 	% all the vars involved
			map(prog_var, alias_set2)
						% the actual mapping
		). 

:- type alias_set2 ---> 
		alias_sel_set(
			int, 		% total number of data structures kept
					% in the data_sets of the map. 
			map(selector,data_set)
		).

:- type data_set --->
		datastructs(
			int, 		% size of the set of data structures.
			set(datastruct)
		).

%-----------------------------------------------------------------------------%
%-- predicate definitions

init(Init) :- Init = init. 
init = alias_set(0, map__init). 
is_empty(alias_set(0, Map)):- map__is_empty(Map). 
		% XXX the test for the empty map shouldn't be necessary. 

size(alias_set(Size, _)) =  Size.

from_pair_alias_list(Aliases, AliasSet):- 
	new_entries(Aliases, init, AliasSet). 

	% Add a list of alias-pairs into the given alias_set. Each alias (A-B)
	% is in fact added twice: once as (A-B), and once as (B-A). 
:- pred new_entries(list(alias)::in, 
		alias_set::in, alias_set::out) is det.
new_entries(Aliases, AliasSet0, AliasSet) :- 
	list__foldl(
		new_entry, 
		Aliases, 
		AliasSet0, 
		AliasSet). 

	% Add a list of alias-pairs into the given alias_set, yet by taking
	% into account the direction of the pairs. I.e. for each alias (A-B),
	% only insert (A-B) and not (B-A) as would have been the case with
	% procedure 'new_entries/3'. 
:- pred new_directed_entries(list(alias)::in, 
		alias_set::in, alias_set::out) is det.
new_directed_entries(Aliases, AliasSet0, AliasSet):- 
	list__foldl(
		pred(A::in, S0::in, S::out) is det:- 
		(
			A = From - To,
			new_directed_entry(From, To, S0, S)
		),
		Aliases, 
		AliasSet0, 
		AliasSet).
			


	% XXX This predicate should first check whether the new alias is not
	% already subsumed by the aliases within the existing alias_set!
	% Currently, this check is not done. 
:- pred new_entry(alias::in, alias_set::in, 
				alias_set::out) is det.
new_entry(Alias, AliasSet0, AliasSet):- 
	Alias = Data1 - Data2, 
	new_directed_entry(Data1, Data2, AliasSet0, AliasSet1), 
	(
		pa_datastruct__equal(Data1, Data2)
	->
		AliasSet = AliasSet1
	;
		new_directed_entry(Data2, Data1, AliasSet1, AliasSet)
	).

:- pred new_directed_entry(datastruct::in, datastruct::in, 
				alias_set::in, alias_set::out) is det.
new_directed_entry(FromData, ToData, AliasSet0, AliasSet):- 
	AliasSet0 = alias_set(Size0, Map0), 
	get_var(FromData, Var), 
	get_selector(FromData, Selector), 
	(
		map__search(Map0, Var, Selectors0)
	->
		alias_set2_new_entry(Selector, ToData, Selectors0, Added, 
				Selectors), 
		(
			Added = yes
		-> 
			map__det_update(Map0, Var, Selectors, Map),
			Size = Size0 + 1
		; 
			Map = Map0, 
			Size = Size0
		)
	;
		alias_set2_empty(Selectors0),
		alias_set2_new_entry(Selector, ToData, Selectors0, 
				Selectors), 
		map__det_insert(Map0, Var, Selectors, Map), 
		Size = Size0 + 1
	), 
	AliasSet = alias_set(Size, Map). 

	% XXX I guess the result is a list in which each alias (A-B) appears
	% twice if A != B, namely as (A-B) and (B-A).
	% XXX Why are sets used here, and then converted to lists? Seems
	% superfluous? 
to_pair_alias_list(AliasSet, Aliases):- 
	AliasSet = alias_set(_, Map), 
	map__to_assoc_list(Map, Pairs), 
	list__foldl(
		pred(Pair::in, S0::in, S::out) is det :- 
		    (
			Pair = Var - Selectors, 
			term__var_to_int(Var, VarInt), 
			alias_set2_unfold(Selectors, SelDatas), 
			list__filter_map(
				pred(SelData::in, Alias::out) is semidet:- 
				    (
					SelData = Selector - Datastruct, 
					pa_datastruct__get_var(Datastruct, 
						DataVar), 
					term__var_to_int(DataVar,
						DataVarInt),
					DataVarInt =< VarInt, 
					pa_datastruct__create(Var, 
						Selector, NewDatastruct), 
					Alias = NewDatastruct - Datastruct
				   ), 
				SelDatas,
				Aliases0), 
			set__insert_list(S0, Aliases0, S)
		   ), 
		Pairs, 
		set__init, 
		AliasesSet), 
	set__to_sorted_list(AliasesSet, Aliases).

project(Vars, AliasSet0, AliasSet):- 
	AliasSet0 = alias_set(_, Map0), 
	map__select(Map0, set__list_to_set(Vars), Map1),
	map__foldl(
		pred(Var::in, SelSet0::in, S0::in, S::out) is det :- 
		    (
			alias_set2_project(Vars, SelSet0, SelSet), 
			(
				alias_set2_empty(SelSet)
			->
				S = S0
			;
		    		S0 = alias_set(Size0, M0), 	
				map__det_insert(M0, Var, SelSet, M),
				Size = Size0 +
					alias_set2_size(SelSet),
				S = alias_set(Size, M)
			)
		   ), 
		Map1, 
		pa_alias_set__init, 
		AliasSet).

	% XXX check where they are used, and avoid these recounts if possible.
	% The counters should be set correctly as soon as the set is altered. 
:- pred recount(alias_set::in, alias_set::out) is det.
recount(AliasSet0, AliasSet):-
	AliasSet0 = alias_set(_, Map), 
	map__foldl(
		pred(_K::in, Selectors::in, 
				Counter0::in, Counter::out) is det :- 
		(
			Counter = Counter0 + alias_set2_size(Selectors)
		), 
		Map, 
		0, 
		Size),	
	AliasSet = alias_set(Size, Map). 

project_set(VarsSet, AliasSet0, AliasSet):-
	set__to_sorted_list(VarsSet, Vars), 
	project(Vars, AliasSet0, AliasSet). 

collect_aliases_of_datastruct(ModuleInfo, ProcInfo, Datastruct, 
			AliasSet, Datastructs):- 
	AliasSet = alias_set(_Size, Map), 
	get_var(Datastruct, Var), 
	proc_info_vartypes(ProcInfo, VarTypes), 
	map__lookup(VarTypes, Var, VarType), 
	get_selector(Datastruct, Selector),
	(
		map__search(Map, Var, SelectorSet)
	->
		alias_set2_collect_aliases(ModuleInfo, VarType, 
				Selector, SelectorSet, Datastructs)
	;
		Datastructs = [] 
	). 

rename(Dict, AliasSet0, AliasSet):-
	AliasSet0 = alias_set(Size, Map0), 
	map__foldl(
		pred(Var0::in, SelectorSet0::in, M0::in, M::out) is det:- 
		    (
			alias_set2_rename(Dict, SelectorSet0,
							SelectorSet1),
			map__lookup(Dict, Var0, Var), 
			(
				map__search(M0, Var, SelectorSet2)
			-> 
				% can occur when 2 vars are renamed to 
				% the same var (call: append(X,X,Y))
				alias_set2_add(SelectorSet1, 
					SelectorSet2, SelectorSet), 
				map__det_update(M0, Var, SelectorSet, M)
			; 
				map__det_insert(M0, Var, SelectorSet1, M)
			)
		   ),
		Map0, 
		map__init, 
		Map),
	AliasSet  = alias_set(Size, Map). 

rename_types(Subst, AliasSet0, AliasSet):- 
	alias_set_map_values(alias_set2_rename_types(Subst), AliasSet0, 
			AliasSet). 

equal(AliasSet0, AliasSet1):-
	AliasSet0 = alias_set(Size, Map0), 
	AliasSet1 = alias_set(Size, Map1), 
	map__keys(Map0, Keys0), 
	map__values(Map0, Values0), 
	equal2(Keys0, Values0, Map1).
:- pred equal2(list(prog_var)::in, list(alias_set2)::in, 
			map(prog_var, alias_set2)::in) is semidet.
equal2([], [], Map) :- map__is_empty(Map). 
equal2([ Var0 | Vars ], [SelectorSet0 | SelectorSets], Map0) :- 
	map__remove(Map0, Var0, SelectorSet1, Map), 
	alias_set2_equal(SelectorSet0, SelectorSet1), 
	equal2(Vars, SelectorSets, Map). 

least_upper_bound(ModuleInfo, ProcInfo, AliasSet0, AliasSet1, AliasSet):-
	AliasSet0 = alias_set(Size0, Map0), 
	AliasSet1 = alias_set(Size1, Map1), 
	(
		Size0 < Size1
	->
		least_upper_bound2(ModuleInfo, ProcInfo, Map0, Map1, AliasSet)
	;
		least_upper_bound2(ModuleInfo, ProcInfo, Map1, Map0, AliasSet)
	).

	% least_upper_bound2(ModuleInfo, ProcInfo, SmallMap, BigMap, Result).
:- pred least_upper_bound2(module_info::in, proc_info::in, 
		map(prog_var, alias_set2)::in, 
		map(prog_var, alias_set2)::in, 
		alias_set::out) is det.

least_upper_bound2(ModuleInfo, ProcInfo, Map0, Map1, AliasSet):- 
	map__foldl(
		pred(Var::in, SelectorSet0::in, M0::in, M::out) is det :- 
		(
			(
				map__search(M0, Var, SelectorSet1)
			->
				proc_info_vartypes(ProcInfo, VarTypes), 
				map__lookup(VarTypes, Var, VarType), 
				alias_set2_least_upper_bound(
					ModuleInfo, VarType, 
					SelectorSet0, SelectorSet1, 
					SelectorSet), 
				map__det_update(M0, Var, SelectorSet, M)
			;
				map__det_insert(M0, Var, SelectorSet0, M)
			)
		),
		Map0,
		Map1, 
		Map),
	recount(alias_set(0, Map), AliasSet). 
	
least_upper_bound_list(ModuleInfo, ProcInfo, List, AliasSet):-
	list__foldl(
		least_upper_bound(ModuleInfo, ProcInfo), 
		List, 
		init,
		AliasSet).

extend(ModuleInfo, ProcInfo, NewAliasSet, OldAliasSet, AliasSet):- 

	% first find the New-Old aliases resulting in an 
	% aliasSet containing only the directional New-Old (stored
	% as Old-New) aliasSet, and the full resulting aliasSet. 
	altclos_two(ModuleInfo, ProcInfo, NewAliasSet, OldAliasSet, 
		OldNewAliasSet, FullOldNewAliasSet), 
	
	% With the OldNewAliasSet, compute the NewOldNewAliasSet 
	% in the same-way. 
	% XXX This seems wrong. Instead of the last argument, the second last
	% should be used, as we only want to use the NewOldNewAliasSet, while 
	% FullNewOldNewAliasSet will contain also OldNewNew combinations,
	% hence, not the alternating closure. 
	% XXX To be checked!!!!
	altclos_two(ModuleInfo, ProcInfo, OldNewAliasSet, NewAliasSet, 
		_, FullNewOldNewAliasSet), 

	list__foldl(
		add,
		[ NewAliasSet, FullOldNewAliasSet, 
		  FullNewOldNewAliasSet ], 
		OldAliasSet, 
		AliasSet).

:- pred altclos_two(module_info::in, proc_info::in, alias_set::in, 
			alias_set::in, alias_set::out, alias_set::out) is det.
altclos_two(ModuleInfo, ProcInfo, NewAliasSet, OldAliasSet, 
					PartialAliasSet, FullResult) :- 
	proc_info_vartypes(ProcInfo, VarTypes), 
	NewAliasSet = alias_set(_, NewMap), 
	OldAliasSet = alias_set(_, OldMap), 
	% compute the common variables
	map__keys(NewMap, NewVars), 
	map__keys(OldMap, OldVars), 
	set__list_to_set(NewVars, NewVarsSet), 
	set__list_to_set(OldVars, OldVarsSet), 
	set__intersect(NewVarsSet, OldVarsSet, CommonVarsSet), 
	set__to_sorted_list(CommonVarsSet, CommonVars), 
	% for each common var, compute the aliases it generates
	list__foldl2(
		pred(Var::in, PM0::in, PM::out, FM0::in, FM::out) is det:- 
		(
			map__lookup(VarTypes, Var, Type), 	
			map__lookup(NewMap, Var, NewSelectorSet), 
			map__lookup(OldMap, Var, OldSelectorSet), 
			pa_alias_set__alias_set2_altclos(ModuleInfo, ProcInfo, 
					Type, NewSelectorSet, OldSelectorSet,
					DirectedAliases), 
				% Directed = FromOld to ToNew
			pa_alias_set__new_directed_entries(DirectedAliases, 
					PM0, PM), 
			pa_alias_set__new_entries(DirectedAliases, 
					FM0, FM) 
		), 
		CommonVars, 
		pa_alias_set__init, 
		PartialAliasSet, 
		pa_alias_set__init, 
		FullResult). 

	% alias_set2_altclos(ModuleInfo, ProcInfo, Type,
	% 			NewSelectorSet, OldSelectorSet, 
	%			OldNewDirectedAliases).
:- pred alias_set2_altclos(module_info::in, proc_info::in, (type)::in, 
				alias_set2::in, alias_set2::in, 
				list(alias)::out) is det.
alias_set2_altclos(ModuleInfo, ProcInfo, Type, 
			NewSelectorSet, OldSelectorSet, 
			DirectedAliases) :- 
	NewSelectorSet = alias_sel_set(_, NewMap), 
	OldSelectorSet = alias_sel_set(_, OldMap), 
	% get the selectors
	map__keys(NewMap, NewSelectors), 
	map__keys(OldMap, OldSelectors), 
	list__foldl(
		pred(NewSel::in, L0::in, L::out) is det:- 
			list__foldl(
				altclos_basic(ModuleInfo, ProcInfo, Type,
					NewMap, OldMap,  
					NewSel), 
				OldSelectors, 
				L0, 
				L),
			NewSelectors, 
			[], 
			DirectedAliases).


:- pred altclos_basic(module_info::in, proc_info::in, (type)::in, 
			map(selector, data_set)::in,
			map(selector, data_set)::in, 
			selector::in, selector::in, 
			list(alias)::in, list(alias)::out) is det.
altclos_basic(ModuleInfo, _ProcInfo, Type, NewMap, OldMap, 
			NewSel, OldSel, 
			AccList, List) :- 
	map__lookup(NewMap, NewSel, NewDataSet0), 
	map__lookup(OldMap, OldSel, OldDataSet0), 
	(
		% NewSel = OldSel.Extension
		pa_selector__less_or_equal(ModuleInfo, NewSel, OldSel, 
			Type, Extension)
	->
		data_set_termshift(OldDataSet0, Extension, OldDataSet), 
		data_set_generate_directed_aliases(OldDataSet, NewDataSet0, 
				NewDirectedAliases)
	;
		% NewSel.Extension = OldSel
		pa_selector__less_or_equal(ModuleInfo, OldSel, NewSel, 
				Type, Extension) 
	->
		data_set_termshift(NewDataSet0, Extension, NewDataSet), 
		data_set_generate_directed_aliases(OldDataSet0, NewDataSet, 
				NewDirectedAliases)
	; 
		NewDirectedAliases = []
	),
	List = append(NewDirectedAliases, AccList).

			
add(AliasSet0, AliasSet1, AliasSet):- 
	AliasSet0 = alias_set(_, Map0), 
	AliasSet1 = alias_set(_, Map1), 

	map__foldl(
		pred(Var::in, SelectorSet0::in, M0::in, M::out) is det:- 
		(
			map__search(M0, Var, SelectorSet1)
		    ->
			alias_set2_add(SelectorSet1, SelectorSet0, 
				SelectorSet), 
			map__det_update(M0, Var, SelectorSet, M)
		    ; 
			map__det_insert(M0, Var, SelectorSet0, M)
		), 
		Map0, 
		Map1, 
		Map), 	
	recount(alias_set(0,Map), AliasSet).
	
normalize(ModuleInfo, ProcInfo, AliasSet0, AliasSet) :- 
	proc_info_vartypes(ProcInfo, VarTypes), 
	AliasSet0 = alias_set(_, Map0), 
	map__foldl(
		pred(Var::in, SelectorSet0::in, M0::in, M::out) is det :- 
		(
			map__lookup(VarTypes, Var, VarType), 
			alias_set2_normalize(ModuleInfo, ProcInfo, VarType, 
				SelectorSet0, SelectorSet), 
			map__det_insert(M0, Var, SelectorSet, M)
		), 
		Map0, 
		map__init, 
		Map), 
	recount(alias_set(0, Map), AliasSet).

less_or_equal(ModuleInfo, ProcInfo, AliasSet1, AliasSet2):- 
	AliasSet1 = alias_set(_, Map1), 
	AliasSet2 = alias_set(_, Map2), 
		% check whether the variable-sets are identical
	set__equal(set__list_to_set(map__keys(Map1)), 
		    set__list_to_set(map__keys(Map2))), 
		% compute the least_upper_bound of both alias_sets
	least_upper_bound(ModuleInfo, ProcInfo, AliasSet1, AliasSet2, 
			AliasSetLUB), 
		% the result should then be equal to the original
		% aliasSet (AliasSet2)
	equal(AliasSet2, AliasSetLUB). 	
	
remove_vars(Vars, AliasSet0, AliasSet):- 
	AliasSet0 = alias_set(_, Map0), 
	map__delete_list(Map0, Vars, Map1), 
	alias_set_map_values(
		alias_set2_remove_vars(Vars), 
		alias_set(0, Map1), 
		AliasSet1), 
	recount(AliasSet1, AliasSet). 


apply_widening(ModuleInfo, ProcInfo, Threshold, AliasSet0, AliasSet, 	
		Widening):- 
	( 
		Threshold \= 0
	-> 
		normalize(ModuleInfo, ProcInfo, AliasSet0, AliasSet01),
		(
			size(AliasSet01) > Threshold
		-> 
			alias_set_map_values_with_key(
				alias_set2_apply_widening(ModuleInfo, ProcInfo),
				AliasSet0, 
				AliasSet1), 
			recount(AliasSet1, AliasSet),
			Widening = yes
		;
			AliasSet = AliasSet0, 
			Widening = no
		)
	; 
		AliasSet = AliasSet0, 
		Widening = no
	).

print(PredInfo, ProcInfo, AliasSet, StartingString, EndString) -->
	print(PredInfo, ProcInfo, AliasSet, StartingString, ", ", EndString).

print(PredInfo, ProcInfo, AliasSet, StartingString, MiddleString, 
		EndString) --> 
	{ to_pair_alias_list(AliasSet, AliasList) },
	io__write_list(AliasList, MiddleString, 
		pa_alias__print(ProcInfo, PredInfo, StartingString, 
			EndString)).


:- pred alias_set_fold(pred(alias_set2, alias_set2), 
				alias_set, alias_set).
:- mode alias_set_fold(pred(in, in) is det, in, out) is det.

alias_set_fold(_Pred, AliasSet, AliasSet). 
	% XXXXXXXXXX

:- pred alias_set_map_values(pred(alias_set2, alias_set2), 
			alias_set, alias_set).
:- mode alias_set_map_values(pred(in, out) is det, in, out) is det.
alias_set_map_values(Pred, AliasSet0, AliasSet) :- 
	AliasSet0 = alias_set(Size, Map0), 
	map__map_values(
		pred(_K::in, S0::in, S::out) is det:-
		(
			Pred(S0, S)
		), 
		Map0, 
		Map),
	AliasSet = alias_set(Size, Map).

:- pred alias_set_map_values_with_key(pred(prog_var, alias_set2, alias_set2), 
			alias_set, alias_set).
:- mode alias_set_map_values_with_key(pred(in, in, out) is det, 
			in, out) is det.
alias_set_map_values_with_key(Pred, AliasSet0, AliasSet) :- 
	AliasSet0 = alias_set(Size, Map0), 
	map__map_values(
		pred(K::in, S0::in, S::out) is det:-
		(
			Pred(K, S0, S)
		), 
		Map0, 
		Map),
	AliasSet = alias_set(Size, Map).
			
	

% internal predicates: 

% alias_set2 = structure to keep track of mappings from selectors unto
% concrete datastructures. 

:- pred alias_set2_empty(alias_set2). 
:- mode alias_set2_empty(out) is det.
:- mode alias_set2_empty(in) is semidet. 
:- func alias_set2_init = alias_set2. 
:- pred alias_set2_new_entry(selector::in, datastruct::in, 
			alias_set2::in, bool::out, alias_set2::out) is det.
:- pred alias_set2_new_entry(selector::in, datastruct::in, 
			alias_set2::in, alias_set2::out) is det.
:- func alias_set2_size(alias_set2) = int.
:- pred alias_set2_unfold(alias_set2::in, 
			list(pair(selector, datastruct))::out) is det.
:- pred alias_set2_project(list(prog_var)::in, alias_set2::in, 
			alias_set2::out) is det.
:- pred alias_set2_rename(map(prog_var, prog_var)::in, 
			alias_set2::in, alias_set2::out) is det.
:- pred alias_set2_rename_types(term__substitution(tvar_type)::in, 
			alias_set2::in, alias_set2::out) is det.
:- pred alias_set2_equal(alias_set2::in, alias_set2::in) is semidet.
:- pred alias_set2_add(alias_set2::in, alias_set2::in, 
			alias_set2::out) is det.
:- pred alias_set2_collect_aliases(module_info::in, (type)::in, 
			selector::in, alias_set2::in, 
			list(datastruct)::out) is det.
:- pred alias_set2_least_upper_bound(module_info::in, (type)::in, 
			alias_set2::in, alias_set2::in, 
			alias_set2::out) is det.
:- pred alias_set2_normalize(module_info::in, proc_info::in, (type)::in, 
			alias_set2::in, alias_set2::out) is det.
:- pred alias_set2_remove_vars(list(prog_var)::in, alias_set2::in, 
			alias_set2::out) is det.
:- pred alias_set2_apply_widening(module_info::in, proc_info::in,
			prog_var::in, alias_set2::in, alias_set2::out) is det.

alias_set2_empty(alias_sel_set(0, map__init)). 
alias_set2_init = AliasSet :- alias_set2_empty(AliasSet). 

alias_set2_new_entry(Selector, Datastruct, AliasSet0, Added, AliasSet):- 
	AliasSet0 = alias_sel_set(Size0, Map0), 
	(
		map__search(Map0, Selector, DataSet0)
	->
		data_set_new_entry(Datastruct, DataSet0, Addition, DataSet), 
		(	
			Addition = yes, 
			Size = Size0 + 1,
			Added = yes
		; 
			Addition = no, 
			Size = Size0, 
			Added = no
		), 
		map__det_update(Map0, Selector, DataSet, Map)
	;
		data_set_empty(EmptyDataSet), 
		data_set_new_entry(Datastruct, EmptyDataSet, DataSet), 
		Size = Size0 + 1, 
		Added = yes,
		map__det_insert(Map0, Selector, DataSet, Map)
	), 
	AliasSet = alias_sel_set(Size, Map). 

alias_set2_new_entry(Selector, Datastruct, AliasSet0, AliasSet):-
	alias_set2_new_entry(Selector, Datastruct, AliasSet0, _, AliasSet).

alias_set2_size(alias_sel_set(Size, _)) = Size. 
alias_set2_unfold(AliasSet, List):- 
	AliasSet = alias_sel_set(_, Map), 
	map__to_assoc_list(Map, Pairs), 
	list__foldl(
		pred(Pair::in, L0::in, L::out) is det:-
		(
			Pair = Selector - DataSet,
			data_set_get_datastructs(DataSet, Datastructs), 
			list__map(
				pred(Datastruct::in, P::out) is det :- 
				(
					P = Selector - Datastruct
				), 
				Datastructs,
				SelectorDatastructs),
			list__append(SelectorDatastructs, L0, L)
		),
		Pairs, 
		[], 
		List).

alias_set2_project(Vars, AliasSet0, AliasSet):-
	AliasSet0 = alias_sel_set(_, Map0), 
	map__foldl(
		pred(Sel0::in, DataSet0::in, M0::in, M::out) is det:-
		(
			data_set_project(Vars, DataSet0, DataSet),
		     	(
				data_set_empty(DataSet)
			->
				M0 = M
			;
				map__det_insert(M0, Sel0, DataSet, M)
			)
		), 
		Map0, 
		map__init, 
		Map), 
	alias_set2_recount(alias_sel_set(0, Map), AliasSet). 

:- pred alias_set2_recount(alias_set2::in, alias_set2::out) is det.
alias_set2_recount(AliasSet0, AliasSet):- 
	AliasSet0 = alias_sel_set(_, Map), 
	map__foldl(
		pred(_K::in, DataSet::in, 
				Counter0::in, Counter::out) is det :- 
		(
			Counter = Counter0 + data_set_size(DataSet)
		), 
		Map, 
		0, 
		Size),	
	AliasSet = alias_sel_set(Size, Map). 

alias_set2_rename(Dict, AliasSet0, AliasSet):- 
	alias_set2_map_values(data_set_rename(Dict), AliasSet0, AliasSet).

alias_set2_rename_types(Subst, AliasSet0, AliasSet):- 
	AliasSet0 = alias_sel_set(Size, Map0), 
	map__foldl(
		pred(Sel0::in, DataSet0::in, M0::in, M::out) is det :-
		(
			pa_selector__rename_types(Subst, Sel0, Sel), 
			data_set_rename_types(Subst, DataSet0, DataSet), 
			map__det_insert(M0, Sel, DataSet, M)
		), 
		Map0,
		map__init, 
		Map), 
	AliasSet = alias_sel_set(Size, Map). 

alias_set2_equal(AliasSet0, AliasSet1):- 
	AliasSet0 = alias_sel_set(Size, Map0), 
	AliasSet1  = alias_sel_set(Size, Map), 
	map__keys(Map0, Keys0),
	map__values(Map0, Values0), 
	alias_set2_equal2(Keys0, Values0, Map). 

:- pred alias_set2_equal2(list(selector)::in, list(data_set)::in, 
			map(selector, data_set)::in) is semidet.
alias_set2_equal2([], [], Map) :- map__is_empty(Map). 
alias_set2_equal2([ Sel0 | Sels ], [ DataSet0 | DataSets ], Map0):-
	map__remove(Map0, Sel0, DataSet1, Map), 
	data_set_equal(DataSet0, DataSet1), 
	alias_set2_equal2(Sels, DataSets, Map).

alias_set2_add(AliasSet0, AliasSet1, AliasSet):- 
	AliasSet0 = alias_sel_set(_, Map0), 
	AliasSet1 = alias_sel_set(_, Map1),
	map__foldl(
		pred(Sel::in, DataSet0::in, M0::in, M::out) is det :-
		(
			(
				map__search(M0, Sel, DataSet1)
			->
				data_set_add(DataSet0, DataSet1, DataSet), 
				map__det_update(M0, Sel, DataSet, M)
			;
				map__det_insert(M0, Sel, DataSet0, M)
			)
		),
		Map0, 
		Map1, 
		Map), 
	alias_set2_recount(alias_sel_set(0, Map), AliasSet).

:- pred alias_set2_map_values(pred(data_set, data_set), 
					alias_set2, alias_set2).
:- mode alias_set2_map_values(pred(in, out) is det, in, out) is det.
alias_set2_map_values(Pred, AliasSet0, AliasSet):- 
	AliasSet0 = alias_sel_set(Size, Map0), 
	map__map_values(
		pred(_K::in, D0::in, D::out) is det :-
		    (Pred(D0, D)), Map0, Map), 
	AliasSet  = alias_sel_set(Size, Map).

alias_set2_collect_aliases(ModuleInfo, Type, 
				Selector, SelectorSet, Datastructs):- 
	SelectorSet = alias_sel_set(_Size, Map), 
	map__foldl(
		pred(Sel::in, DataSet0::in, Data0::in, Data::out) is det:-
		(
			% if Sel is more general than Selector, i.e.
			% Selector = Sel.Extension, apply this extension
			% to all the datastructs associated with that Sel.
			(
				less_or_equal(ModuleInfo,  Selector,
					Sel, Type, Extension)
			->
				data_set_termshift(DataSet0, Extension, 
					DataSet),
				data_set_add(Data0, DataSet, Data)
			;
				Data = Data0
			)
		), 
		Map, 
		data_set_empty, 
		CollectedDataSet), 
	data_set_get_datastructs(CollectedDataSet, Datastructs).

alias_set2_least_upper_bound(ModuleInfo, Type, 
		SelectorSet0, SelectorSet1, SelectorSet):- 
	SelectorSet0 = alias_sel_set(_Size0, Map0), 
	SelectorSet1 = alias_sel_set(_Size1, Map1),
	map__foldl(
		alias_set2_lub(ModuleInfo, Type),
		Map0, 
		Map1,
		Map),
	alias_set2_add(alias_sel_set(0,Map), SelectorSet0, SelectorSet).

	% alias_set2_lub(ModuleInfo, Type, Pair, Map0, Map):-
	% Least upper bound between a real selectorset (Map0), and one
	% single entry of another selectorset (Pair).
	% precondition: the first selectorset is minimal (i.e., does
	% not contain superfluous entries, e.g. Hv1/[] - Hv2/[] and
	% in the same time Hv1/el - Hv2/el .
:- pred alias_set2_lub(module_info::in, (type)::in,
			selector::in, data_set::in, 
			map(selector, data_set)::in, 
			map(selector, data_set)::out) is det.
alias_set2_lub(ModuleInfo, Type, Sel0, DataSet0, M0, M):- 
	map__keys(M0, Selectors), 
	list__foldl2(
		alias_set2_lub2(ModuleInfo, Type, Sel0),	
		Selectors, 
		DataSet0, 
		DataSet,
		M0, 
		M1), 
	% and finally, add what is remaining of DataSet
	(
		data_set_empty(DataSet)
	->
		M = M1
	; 
		(
			map__search(M1, Sel0, DataSetA)
		->
			data_set_add(DataSetA, DataSet, DataSetNew),
			map__det_update(M1, Sel0, DataSetNew, M)
		;	
			map__det_insert(M1, Sel0, DataSet0, M)
		)
	).

	% alias_set2_lub2(ModuleInfo, Type, FirstSel0, OtherSel,
	% 			FirstDataSet0, FirstDataSet,
	%			OtherMap0, OtherMap). 
	% OtherSel is a selector from OtherMap0. FirstDataSet0 corresponds
	% with FirstSel0, and comes from a first SelectorSet. 
:- pred alias_set2_lub2(module_info::in, (type)::in,
			selector::in, selector::in, 
			data_set::in, data_set::out, 
			map(selector, data_set)::in, 
			map(selector, data_set)::out) is det.
alias_set2_lub2(ModuleInfo, Type, FirstSel0, OtherSel, 
			FirstDataSet0, FirstDataSet, 
			OtherMap0, OtherMap):- 
	(
		data_set_empty(FirstDataSet0)
	->
		FirstDataSet = FirstDataSet0, 
		OtherMap = OtherMap0
	; 
		(
			% FirstSel0 = OtherSel.Extension
			pa_selector__less_or_equal(ModuleInfo, 
				FirstSel0, OtherSel, Type, Extension)
		->
			map__lookup(OtherMap0, OtherSel, OtherDataSet0), 
			data_set_termshift(OtherDataSet0, Extension, 
					OtherDataSetOTS),
				% remove the OtherDataSetOTS entries from
				% FirstDataSet0
			data_set_difference(FirstDataSet0, OtherDataSetOTS, 
						FirstDataSet), 
			OtherMap = OtherMap0
		;
			pa_selector__less_or_equal(ModuleInfo, 
				OtherSel, FirstSel0, Type, Extension)
		->
			map__lookup(OtherMap0, OtherSel, OtherDataSet0), 
			data_set_termshift(FirstDataSet0, Extension, 
						FirstDataSet0TS), 
			data_set_difference(OtherDataSet0, 
						FirstDataSet0TS, 
						OtherDataSet), 
			map__det_update(OtherMap0, OtherSel, OtherDataSet, 
						OtherMap),
			FirstDataSet = FirstDataSet0
		;
			FirstDataSet = FirstDataSet0, 
			OtherMap = OtherMap0
		)
	).
		

alias_set2_normalize(ModuleInfo, ProcInfo, Type, SelectorSet0, 
				SelectorSet):- 
	SelectorSet0 = alias_sel_set(_, Map0), 
	map__foldl(
		pred(Sel0::in, DataSet0::in, M0::in, M::out) is det:- 
		(
			pa_selector__normalize_wti(Type, ModuleInfo, 
					Sel0, Sel0Norm), 
			data_set_normalize(ModuleInfo, ProcInfo,  
					DataSet0, DataSet1), 
			(
				map__search(M0, Sel0Norm, DataSetM)
			->
				data_set_add(DataSetM, DataSet1, DataSet), 
				map__det_update(M0, Sel0Norm, DataSet, M)
			;
				map__det_insert(M0, Sel0Norm, DataSet1, M)
			)
		),
		Map0, 
		map__init, 
		Map),
	alias_set2_recount(alias_sel_set(0, Map), SelectorSet). 
		

alias_set2_remove_vars(Vars, SelectorSet0, SelectorSet):- 
	SelectorSet0 = alias_sel_set(_, Map0), 
	map__foldl(
		pred(Sel0::in, DataSet0::in, M0::in, M::out) is det :- 
		(
			data_set_remove_vars(Vars, DataSet0, DataSet), 
			(
				data_set_empty(DataSet)
			-> 
				M = M0
			;
				map__det_insert(M0, Sel0, DataSet, M)
			)
		), 
		Map0, 
		map__init, 
		Map), 
	alias_set2_recount(alias_sel_set(0, Map), SelectorSet).

alias_set2_apply_widening(ModuleInfo, ProcInfo, ProgVar, 
		SelectorSet0, SelectorSet):- 
	SelectorSet0 = alias_sel_set(_, Map0), 
	map__foldl(
		pred(Sel0::in, DataSet0::in, M0::in, M::out) is det:- 
		(
			% widening of the associated datastructures
			data_set_apply_widening(ModuleInfo, ProcInfo, 
				DataSet0, DataSet1), 

			% widening of the selector
			pa_datastruct__create(ProgVar, Sel0, Data0), 
			pa_datastruct__apply_widening(ModuleInfo, 
				ProcInfo, Data0, Data), 
			pa_datastruct__get_selector(Data, Sel), 

			% regroup the widened dataset with the dataset
			% that is associated with the widened Sel, as this
			% Sel might already be in M0. 
			(
				map__search(M0, Sel, DataSetOld)
			->
				% XXX should also take subsumption into 
				% account !
				data_set_add(DataSet1, DataSetOld, DataSet)
			;
				DataSet = DataSet1
			), 
			map__set(M0, Sel, DataSet, M)
		),
		Map0,
		map__init, 
		Map1), 
	% the precaution of checking whether the widened selector might
	% already be present in the built-up map might not be enough. 
	% A last check is necessary to be sure that there are no
	% selectors which are subsumed by other selectors in the list. 
	proc_info_vartypes(ProcInfo, VarTypes), 
	map__lookup(VarTypes, ProgVar, VarType), 
	alias_set2_least_upper_bound(ModuleInfo, VarType, 
		alias_sel_set(0, Map1), alias_set2_init, SelectorSet). 


% data_set

:- pred data_set_empty(data_set).
:- func data_set_empty = data_set. 
:- mode data_set_empty(out) is det.
:- mode data_set_empty(in) is semidet. 

:- pred data_set_new_entry(datastruct::in, data_set::in, 
				bool::out, data_set::out) is det.
:- pred data_set_new_entry(datastruct::in, data_set::in, data_set::out) is det.
:- pred data_set_member(datastruct::in, data_set::in) is semidet.
:- func data_set_size(data_set) = int.
:- pred data_set_get_datastructs(data_set::in, list(datastruct)::out) is det.
:- pred data_set_project(list(prog_var)::in, 
				data_set::in, data_set::out) is det.
:- pred data_set_rename(map(prog_var, prog_var)::in, 
				data_set::in, data_set::out) is det.
:- pred data_set_rename_types(term__substitution(tvar_type)::in, 
				data_set::in, data_set::out) is det.
:- pred data_set_equal(data_set::in, data_set::in) is semidet.
:- pred data_set_add(data_set::in, data_set::in, data_set::out) is det.
:- pred data_set_termshift(data_set::in, selector::in, data_set::out) is det.
:- pred data_set_normalize(module_info::in, proc_info::in, 
				data_set::in, data_set::out) is det.
:- pred data_set_generate_directed_aliases(data_set::in, 
				data_set::in, list(alias)::out) is det.
:- pred data_set_remove_vars(list(prog_var)::in, data_set::in, 
				data_set::out) is det.
	% data_set_difference(A, B, C):- C = A - B. 
:- pred data_set_difference(data_set::in, data_set::in, 
				data_set::out) is det.
:- pred data_set_apply_widening(module_info::in, proc_info::in, 
				data_set::in, data_set::out) is det.

data_set_empty(datastructs(0, set__init)). 
data_set_empty = D :- data_set_empty(D).
data_set_new_entry(Data, DataSet0, NewAddition, DataSet):-
	DataSet0 = datastructs(Size0, Datastructs0), 
	(
		set__member(Data, Datastructs0)
	-> 
		NewAddition = bool__no, 
		DataSet = DataSet0
	; 
		set__insert(Datastructs0, Data, Datastructs), 
		Size = Size0 + 1, 
		NewAddition = bool__yes, 
		DataSet = datastructs(Size, Datastructs)
	).
data_set_new_entry(Data, DataSet0, DataSet) :-
	data_set_new_entry(Data, DataSet0, _, DataSet). 
data_set_member(Data, DataSet) :- 
	DataSet = datastructs(N, DataStructs), 
	N \= 0,
	set__member(Data, DataStructs). 
data_set_size(datastructs(Size,_)) = Size. 
data_set_get_datastructs(DataSet, ListDatastructs):- 
	DataSet = datastructs(_, SetDatastructs), 
	set__to_sorted_list(SetDatastructs, ListDatastructs). 
data_set_project(Vars, DataSet0, DataSet):-
	data_set_filter(
		pred(Data::in) is semidet :- 
		(
			get_var(Data, Var), 
			list__member(Var, Vars)
		),
		DataSet0, 
		DataSet). 
data_set_rename(Dict, DataSet0, DataSet) :- 
	data_set_map(pa_datastruct__rename(Dict), DataSet0, DataSet).
data_set_rename_types(Subst, DataSet0, DataSet):-
	data_set_map(pa_datastruct__rename_types(Subst), 
			DataSet0, DataSet). 
data_set_equal(DataSet0, DataSet1):-
	DataSet0 = datastructs(Size0, Data0), 
	DataSet1 = datastructs(Size0, Data1), 
	set__to_sorted_list(Data0, LData0), 
	set__to_sorted_list(Data1, LData1), 
	list__foldl(
		ho_delete(pa_datastruct__equal), 
		LData0, 
		LData1, 
		[]). 

	% ho_delete(EqualityTest, Elem, List0, List): delete element Elem
	% from the given list (List0) using the EqualityTest. 
:- pred ho_delete(pred(T, T), T, list(T), list(T)).
:- mode ho_delete(pred(in, in) is semidet, in, in, out) is semidet.
ho_delete(Equal, Elem, List0, List) :- 
	List0 = [ H | T ],
	(
		Equal(Elem, H)
	->
		List = T 
	; 
		ho_delete(Equal, Elem, T, Rest), 
		List = [ H | Rest ]
	).

data_set_add(DataSet0, DataSet1, DataSet) :- 
	DataSet0 = datastructs(_Size0, Data0), 
	DataSet1 = datastructs(_Size1, Data1), 
	Data = set__union(Data0, Data1), 
	DataSet = datastructs(set__count(Data), Data). 

data_set_termshift(DataSet0, Sel, DataSet):- 
	data_set_map(
		pred(D0::in, D::out) is det :- 
		(
			pa_datastruct__termshift(D0, Sel, D)
		),
		DataSet0, 
		DataSet).

	% higher order predicates for handling data_set's.
:- pred data_set_map(pred(datastruct, datastruct), data_set, data_set).
:- mode data_set_map(pred(in, out) is det, in, out) is det.
data_set_map(Pred, DataSet0, DataSet):-
	DataSet0 = datastructs(_Size, Datastructs0), 
	Datastructs = set__map(tofunc(Pred), Datastructs0),
	DataSet = datastructs(set__count(Datastructs), Datastructs). 

:- func tofunc(pred(X,Y), X) = Y.
:- mode tofunc(pred(in,out) is det, in) = out is det.

tofunc(Pred, X) = Y :- Pred(X, Y).

:- pred data_set_filter(pred(datastruct), data_set, data_set).
:- mode data_set_filter(pred(in) is semidet, in, out) is det.
data_set_filter(Pred, DataSet0, DataSet):- 
	DataSet0 = datastructs(_, Datastructs0), 
	Datastructs = set__filter(Pred, Datastructs0),
	DataSet = datastructs(set__count(Datastructs), Datastructs).

data_set_normalize(ModuleInfo, ProcInfo, DataSet0, DataSet):- 
	data_set_map(
		pa_datastruct__normalize_wti(ProcInfo, ModuleInfo), 
		DataSet0, 
		DataSet). 

data_set_generate_directed_aliases(FromDataSet, ToDataSet, Aliases):- 
	FromDataSet = datastructs(_, FromData), 
	ToDataSet   = datastructs(_, ToData), 
	set_cross_product(FromData, ToData, AliasesSet), 
	set__to_sorted_list(AliasesSet, Aliases).

data_set_remove_vars(Vars, DataSet0, DataSet):- 
	data_set_filter(
		pred(DataStruct::in) is semidet :- 
		(
			get_var(DataStruct, Var), 
			\+ list__member(Var, Vars)
		), 
		DataSet0, 
		DataSet). 

data_set_difference(DataSet1, DataSet2, DataSet):-
	DataSet1 = datastructs(_, Data1), 
	DataSet2 = datastructs(_, Data2), 
	Data = set__difference(Data1, Data2), 
	DataSet = datastructs(set__count(Data), Data).

data_set_apply_widening(ModuleInfo, ProcInfo, DataSet0, DataSet):- 
	DataSet0 = datastructs(_, Data0), 
	% XXX should also take subsumption into account ! 
	Data = set__map(pa_datastruct__apply_widening(ModuleInfo, ProcInfo), 
			Data0),
	DataSet = datastructs(set__count(Data), Data). 
	
	
:- pred set_cross_product(set(T1)::in, set(T2)::in, 
				set(pair(T1, T2))::out) is det.

set_cross_product(Set0, Set1, CrossProduct):-
	solutions_set(
		pred(Pair::out) is nondet :- 
		(
			set__member(Elem0, Set0), 
			set__member(Elem1, Set1), 
			Pair = Elem0 - Elem1
		), 
		CrossProduct).

%-----------------------------------------------------------------------------%

