%-----------------------------------------------------------------------------%
% Copyright (C) 2001-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_alias_set: defines the datastructure alias_set which represents
%		       a set of aliases. This module will replace the
%		       module pa_alias which only took care of representing
% 		       one single alias. In this new representation we will
%		       not represent single aliases anymore. 
% main author: nancy

% TO DO: 
% 	- record type of the selectorset immediately in the set. 

:- module pa_alias_set. 

:- interface.

%-----------------------------------------------------------------------------%
%-- import_module

% library modules
:- import_module list, set, map, io, term.

% XXX parent modules
:- import_module hlds, parse_tree. 
% compiler modules
:- import_module pa_datastruct. 
:- import_module hlds__hlds_module, hlds__hlds_pred.
:- import_module parse_tree__prog_data. 
:- import_module pa_alias.


%-----------------------------------------------------------------------------%
%-- exported types

:- type alias_set. 
% :- type alias == pair(pa_datastruct__datastruct, pa_datastruct__datastruct).

%-----------------------------------------------------------------------------%
%-- exported predicates

:- pred init(alias_set::out) is det.
:- func init = alias_set is det. 
:- pred is_empty(alias_set::in) is semidet.
:- pred get_size(alias_set::in, int::out) is det.

	% conversion between list of aliases to alias_set's
:- pred from_pair_alias_list(list(alias)::in, alias_set::out) is det.
:- pred to_pair_alias_list(alias_set::in, list(alias)::out) is det.

	% projection-operations. Given a list or set of prog_vars, 
	% keep only that part of the alias_set which relates to those
	% prog_vars. 
:- pred project(list(prog_var)::in, alias_set::in, alias_set::out) is det. 
:- pred project_set(set(prog_var)::in, alias_set::in, 
		alias_set::out) is det.

	% compute all the datastructures to which a certain datastruct
	% is aliased. This returns a list of datastructs. 
:- pred collect_aliases_of_datastruct(module_info::in, proc_info::in, 
		pa_datastruct__datastruct::in, alias_set::in,
		list(pa_datastruct__datastruct)::out) is det.

	% rename the prog_vars occurring in the alias_set, using
	% a map which maps the to-be-replaced-vars with unto the
	% new prog_vars. 
:- pred rename(map(prog_var,prog_var)::in, alias_set::in, 
		alias_set::out) is det. 
	
	% rename the types occurring in the alias_set, applying
	% the given substitution to each of the types encountered. 
:- pred rename_types(term__substitution(tvar_type)::in, 
		alias_set::in, alias_set::out) is det.

	% equality test. Needed for the fixpoint computation. 
:- pred equal(alias_set::in, alias_set::in) is semidet. 

	% compute the least upper bound of alias_sets.
:- pred least_upper_bound(module_info::in, proc_info::in, 
		alias_set::in, alias_set::in, alias_set::out) is det.
:- pred least_upper_bound_list(module_info::in, proc_info::in, 
		list(alias_set)::in, alias_set::out) is det.

	% extend(ModuleInfo, ProcInfo, NewAliasSet, OldAliasSet, 
	%			ComputedAliasSet). 
	% Extend a given OldAliasSet with the information contained
	% in the NewAliasSet. Note that order here is very important!
	% The NewAliasSet is the alias_set which was computed for
	% one specific atom. This information needs to be computed
	% with the aliases which already existed at the program point
	% corresponding with this atom (the OldAliasSet). 
	% ==> alternating closure.
:- pred extend(module_info::in, proc_info::in, alias_set::in, 
		alias_set::in, alias_set::out) is det.

	% add two alias_sets together without bothering to extend
	% one against the other. 
:- pred add(alias_set::in, alias_set::in, alias_set::out) is det.
	
	% normalize all the selectors within the alias_set and
	% simplify if necessary. 
:- pred normalize(module_info::in, proc_info::in,  
		alias_set::in, alias_set::out) is det.

	% less_or_equal(ModuleInfo, ProcInfo, AliasSet1, AliasSet2). 
:- pred less_or_equal(module_info::in, proc_info::in, 
		alias_set::in, alias_set::in) is semidet.

	% remove all the information regading the given list of
	% variables. 
:- pred remove_vars(list(prog_var)::in, alias_set::in, 
		alias_set::out) is det. 

:- pred apply_widening(module_info::in, proc_info::in, alias_set::in, 
		alias_set::out) is det.

	% printing predicates

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

%-----------------------------------------------------------------------------%
%-- import module

% library modules
:- import_module std_util.
:- import_module int, bool, assoc_list. 

% compiler modules
:- import_module pa_selector.

%-----------------------------------------------------------------------------%
%-- type definitions

	% the alias set is represented as a mapping: each prog_var is
	% associated with a new set representing the structures with 	
	% which is aliased. 
:- type alias_set ---> 
		alias_set(
			int, 		% total number of aliases 
						% represented by this set.
%			set(prog_var), 	% all the vars involved
			map(prog_var, alias_set2)
						% the actual mapping
		). 

	% the structures with which a variable can be aliased are
	% represented by a new mapping: for each selector of that
	% precise variable, we keep track of the datastructures
	% with which it is aliased. 
:- type alias_set2 ---> 
		alias_sel_set(
			int, 
			map(selector,data_set)
		).

:- type data_set --->
		datastructs(
			int, 
			set(datastruct)
		).

%-----------------------------------------------------------------------------%
%-- predicate definitions

pa_alias_set__init(Init) :- Init = pa_alias_set__init. 
pa_alias_set__init = alias_set(0, map__init). 
pa_alias_set__is_empty(alias_set(0, Map)):- map__is_empty(Map). 
pa_alias_set__get_size(alias_set(Size, _) , Size).

pa_alias_set__from_pair_alias_list(Aliases, AliasSet):- 
	pa_alias_set__new_entries(Aliases, pa_alias_set__init, AliasSet). 

:- pred pa_alias_set__new_entries(list(alias)::in, 
		alias_set::in, alias_set::out) is det.
pa_alias_set__new_entries(Aliases, AliasSet0, AliasSet) :- 
	list__foldl(
		pa_alias_set__new_entry, 
		Aliases, 
		AliasSet0, 
		AliasSet). 

	% Alias = From - To
	% This will be entered as From = Var - Selector --> To in DataSet
:- pred pa_alias_set__new_directed_entries(list(alias)::in, 
		alias_set::in, alias_set::out) is det.
pa_alias_set__new_directed_entries(Aliases, AliasSet0, AliasSet):- 
	list__foldl(
		pred(A::in, S0::in, S::out) is det:- 
		(
			A = From - To,
			pa_alias_set__new_entry(From, To, S0, S)
		),
		Aliases, 
		AliasSet0, 
		AliasSet).
			


:- pred pa_alias_set__new_entry(alias::in, alias_set::in, 
				alias_set::out) is det.
pa_alias_set__new_entry(Alias, AliasSet0, AliasSet):- 
	Alias = Data1 - Data2, 
	pa_alias_set__new_entry(Data1, Data2, AliasSet0, AliasSet1), 
	(
		pa_datastruct__equal(Data1, Data2)
	->
		AliasSet = AliasSet1
	;
		pa_alias_set__new_entry(Data2, Data1, AliasSet1, AliasSet)
	).

:- pred pa_alias_set__new_entry(datastruct::in, datastruct::in, 
				alias_set::in, alias_set::out) is det.
pa_alias_set__new_entry(FromData, ToData, AliasSet0, AliasSet):- 
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
		map_det_insert(Map0, Var, Selectors, Map, 
				"(pa_alias_set) pa_alias_set__new entry/4"), 
		Size = Size0 + 1
	), 
	AliasSet = alias_set(Size, Map). 

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
		pred(Var::in, SelSet0::in, M0::in, M::out) is det :- 
		    (
			alias_set2_project(Vars, SelSet0, SelSet), 
			(
				alias_set2_empty(SelSet)
			->
				M = M0
			;
				map_det_insert(M0, Var, SelSet, M, 
				"(pa_alias_set) project/3")
			)
		   ), 
		Map1, 
		map__init, 
		Map), 
	recount(alias_set(0, Map), AliasSet).
		

:- pred pa_alias_set__recount(alias_set::in, alias_set::out) is det.

pa_alias_set__recount(AliasSet0, AliasSet):-
	AliasSet0 = alias_set(_, Map), 
	map__foldl(
		pred(_K::in, Selectors::in, 
				Counter0::in, Counter::out) is det :- 
		(
			alias_set2_get_size(Selectors, S), 
			Counter = Counter0 + S 
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
				map_det_insert(M0, Var, SelectorSet1, M, 
				"(pa_alias_set) rename/3")
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
	map__keys(Map0, Vars), 
	list__foldl(
		pred(Var::in, M0::in, M::out) is det :- 
		(
			map__lookup(Map0, Var, SelectorSet0), 
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
				map_det_insert(M0, Var, SelectorSet0, M, 
				"(pa_alias_set) least_upper_bound2/5")
			)
		),
		Vars,
		Map1, 
		Map),
	pa_alias_set__recount(alias_set(0, Map), AliasSet). 
	
least_upper_bound_list(ModuleInfo, ProcInfo, List, AliasSet):-
	list__foldl(
		least_upper_bound(ModuleInfo, ProcInfo), 
		List, 
		pa_alias_set__init,
		AliasSet).

extend(ModuleInfo, ProcInfo, NewAliasSet, OldAliasSet, AliasSet):- 

	% first find the New-Old aliases resulting in an 
	% aliasSet containing only the directional New-Old (stored
	% as Old-New) aliasSet, and the full resulting aliasSet. 
	altclos_two(ModuleInfo, ProcInfo, NewAliasSet, OldAliasSet, 
		OldNewAliasSet, FullOldNewAliasSet), 
	
	% With the OldNewAliasSet, compute the NewOldNewAliasSet 
	% in the same-way. 
	altclos_two(ModuleInfo, ProcInfo, OldNewAliasSet, NewAliasSet, 
		_, FullNewOldNewAliasSet), 

	list__foldl(
		pa_alias_set__add,
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
			alias_set2_altclos(ModuleInfo, ProcInfo, 
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
			map_det_insert(M0, Var, SelectorSet0, M, 
				"(pa_alias_set) add/3")
		), 
		Map0, 
		Map1, 
		Map), 	
	pa_alias_set__recount(alias_set(0,Map), AliasSet).
	
normalize(ModuleInfo, ProcInfo, AliasSet0, AliasSet) :- 
	proc_info_vartypes(ProcInfo, VarTypes), 
	AliasSet0 = alias_set(_, Map0), 
	map__keys(Map0, Vars), 
	list__foldl(
		pred(Var::in, M0::in, M::out) is det :- 
		(
			map__lookup(Map0, Var, SelectorSet0), 
			map__lookup(VarTypes, Var, VarType), 
			alias_set2_normalize(ModuleInfo, ProcInfo, VarType, 
				SelectorSet0, SelectorSet), 
			map_det_insert(M0, Var, SelectorSet, M, 
				"(pa_alias_set) normalize/4")
		), 
		Vars, 
		map__init, 
		Map), 
	pa_alias_set__recount(alias_set(0, Map), AliasSet).

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


apply_widening(ModuleInfo, ProcInfo, AliasSet0, AliasSet):- 
	alias_set_map_values_with_key(
		alias_set2_apply_widening(ModuleInfo, ProcInfo),
		AliasSet0, 
		AliasSet1), 
	recount(AliasSet1, AliasSet). 
	

print(PredInfo, ProcInfo, AliasSet, StartingString, EndString) -->
	print(PredInfo, ProcInfo, AliasSet, StartingString, ", ", EndString).

print(PredInfo, ProcInfo, AliasSet, StartingString, MiddleString, 
		EndString) --> 
	{ pa_alias_set__to_pair_alias_list(AliasSet, AliasList) },
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
:- pred alias_set2_get_size(alias_set2::in, int::out) is det.
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
		map_det_insert(Map0, Selector, DataSet, Map, 
			"(pa_alias_set) alias_set2_new_entry/5")
	), 
	AliasSet = alias_sel_set(Size, Map). 

alias_set2_new_entry(Selector, Datastruct, AliasSet0, AliasSet):-
	alias_set2_new_entry(Selector, Datastruct, AliasSet0, _, AliasSet).

alias_set2_get_size(alias_sel_set(Size, _), Size). 
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
				map_det_insert(M0, Sel0, DataSet, M, 
				"(pa_alias_set) alias_set2_project/3")
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
			data_set_get_size(DataSet, S), 
			Counter = Counter0 + S 
		), 
		Map, 
		0, 
		Size),	
	AliasSet = alias_sel_set(Size, Map). 

alias_set2_rename(Dict, AliasSet0, AliasSet):- 
	alias_set2_map_values(data_set_rename(Dict), AliasSet0, AliasSet).

alias_set2_rename_types(Subst, AliasSet0, AliasSet):- 
	AliasSet0 = alias_sel_set(Size, Map0), 
	map__to_assoc_list(Map0, AssocList0), 
	list__foldl(
		pred(Pair::in, M0::in, M::out) is det :-
		(
			Pair = Sel0 - DataSet0, 
			pa_selector__rename_types(Subst, Sel0, Sel), 
			data_set_rename_types(Subst, DataSet0, DataSet), 
			map__det_insert(M0, Sel, DataSet, M)
		), 
		AssocList0, 
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
	map__to_assoc_list(Map0, Pairs), 
	list__foldl(
		pred(Pair::in, M0::in, M::out) is det :-
		(
			Pair = Sel - DataSet0, 
			(
				map__search(M0, Sel, DataSet1)
			->
				data_set_add(DataSet0, DataSet1, DataSet), 
				map__det_update(M0, Sel, DataSet, M)
			;
				map__det_insert(M0, Sel, DataSet0, M)
			)
		),
		Pairs, 
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
	map__keys(Map, Selectors), 
	list__foldl(
		pred(Sel::in, Data0::in, Data::out) is det:-
		(
			% if Sel is more general than Selector, i.e.
			% Selector = Sel.Extension, apply this extension
			% to all the datastructs associated with that Sel.
			(
				less_or_equal(ModuleInfo,  Selector,
					Sel, Type, Extension)
			->
				map__lookup(Map, Sel, DataSet0), 
				data_set_termshift(DataSet0, Extension, 
					DataSet),
				data_set_add(Data0, DataSet, Data)
			;
				Data = Data0
			)
		), 
		Selectors, 
		data_set_empty, 
		CollectedDataSet), 
	data_set_get_datastructs(CollectedDataSet, Datastructs).

alias_set2_least_upper_bound(ModuleInfo, Type, 
		SelectorSet0, SelectorSet1, SelectorSet):- 
	SelectorSet0 = alias_sel_set(_Size0, Map0), 
	SelectorSet1 = alias_sel_set(_Size1, Map1),
	map__to_assoc_list(Map0, Assoc0), 
	list__foldl(
		alias_set2_lub(ModuleInfo, Type),
		Assoc0, 
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
			pair(selector,data_set)::in, 
			map(selector, data_set)::in, 
			map(selector, data_set)::out) is det.
alias_set2_lub(ModuleInfo, Type, Pair0, M0, M):- 
	map__keys(M0, Selectors), 
	Pair0 = Sel0 - DataSet0,
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
	map__keys(Map0, Selectors), 
	list__foldl(
		pred(Sel0::in, M0::in, M::out) is det:- 
		(
			pa_selector__normalize_wti(Type, ModuleInfo, 
					Sel0, Sel0Norm), 
			map__lookup(Map0, Sel0, DataSet0), 
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
		Selectors, 
		map__init, 
		Map),
	alias_set2_recount(alias_sel_set(0, Map), SelectorSet). 
		

alias_set2_remove_vars(Vars, SelectorSet0, SelectorSet):- 
	SelectorSet0 = alias_sel_set(_, Map0), 
	map__keys(Map0, Selectors0), 
	list__foldl(
		pred(Sel0::in, M0::in, M::out) is det :- 
		(
			map__lookup(Map0, Sel0, DataSet0),
			data_set_remove_vars(Vars, DataSet0, DataSet), 
			(
				data_set_empty(DataSet)
			-> 
				M = M0
			;
				map__det_insert(M0, Sel0, DataSet, M)
			)
		), 
		Selectors0, 
		map__init, 
		Map), 
	alias_set2_recount(alias_sel_set(0, Map), SelectorSet).

alias_set2_apply_widening(ModuleInfo, ProcInfo, ProgVar, 
		SelectorSet0, SelectorSet):- 
	SelectorSet0 = alias_sel_set(_, Map0), 
	map__keys(Map0, Selectors),
	list__foldl(
		pred(Sel0::in, M0::in, M::out) is det:- 
		(
			% widening of the associated datastructures
			map__lookup(Map0, Sel0, DataSet0), 
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
		Selectors,
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
:- pred data_set_get_size(data_set::in, int::out) is det.
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
data_set_get_size(DataSet, Size):- 
	DataSet = datastructs(Size, _). 
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

:- import_module require, string. 
:- pred map_det_insert(map(K,V)::in, K::in, V::in, 
			map(K,V)::out, string::in) is det.
map_det_insert(Map0, K, V, Map, Msg) :- 
	(
		map__insert(Map0, K, V, Map1)
	->
		Map = Map1
	; 
		string__append_list([ Msg, ": map_det_insert-problem"], Msg2),
		require__error(Msg2)
	). 

