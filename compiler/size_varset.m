%---------------------------------------------------------------------------%
% Copyright (C) 1993-1998 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%
%
% File: size_varset.m.
% Main author: vjteag.
% Stability: low.
%
% This file is a copy of varset.m.
%
% This file provides facilities for manipulating collections of
% size_variables and terms.
% It provides the 'size_varset' ADT. A size_varset is a set of size_variables.
% (These size_variables are object-level size_variables, and are represented
% as ground terms, so it might help to think of them as "size_variable ids"
% rather than size_variables.)
% Associated with each size_variable there can be both a name and a value
% (binding).
%
% There may be some design flaws in the relationship between size_varset.m,
% term.m, and graph.m.  Once we have implemented unique modes and
% destructive assignment, we will need to rethink the design;  we may
% end up modifying these modules considerably, or we may end up
% making new single-threaded versions of these modules.
%
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- module size_varset.
:- interface.
:- import_module list.

:- type size_var.
:- type size_varset.
:- type size_var_supply.

	% construct an empty size_varset.
:- pred size_varset__init(size_varset).
:- mode size_varset__init(out) is det.

	% check whether a size_varset is empty.
:- pred size_varset__is_empty(size_varset).
:- mode size_varset__is_empty(in) is semidet.

	% create a new size_variable
:- pred size_varset__new_var(size_varset, size_var, size_varset).
:- mode size_varset__new_var(in, out, out) is det.

	% create a new named size_variable
:- pred size_varset__new_named_var(size_varset, string, size_var, size_varset).
:- mode size_varset__new_named_var(in, in, out, out) is det.

	% create multiple new size_variables
:- pred size_varset__new_vars(size_varset, int, list(size_var), size_varset).
:- mode size_varset__new_vars(in, in, out, out) is det.

	% delete the name and value for a size_variable
:- pred size_varset__delete_var(size_varset, size_var, size_varset).
:- mode size_varset__delete_var(in, in, out) is det.

	% delete the names and values for a list of size_variables
:- pred size_varset__delete_vars(size_varset, list(size_var), size_varset).
:- mode size_varset__delete_vars(in, in, out) is det.

	% return a list of all the size_variables in a size_varset
:- pred size_varset__vars(size_varset, list(size_var)).
:- mode size_varset__vars(in, out) is det.

	% set the name of a size_variable
:- pred size_varset__name_var(size_varset, size_var, string, size_varset).
:- mode size_varset__name_var(in, in, in, out) is det.

	% lookup the name of a size_variable;
	% create one if it doesn't have one using V_ as a prefix
:- pred size_varset__lookup_name(size_varset, size_var, string).
:- mode size_varset__lookup_name(in, in, out) is det.

	% lookup the name of a size_variable;
	% create one if it doesn't have one using the specified prefix
:- pred size_varset__lookup_name(size_varset, size_var, string, string).
:- mode size_varset__lookup_name(in, in, in, out) is det.

	% lookup the name of a size_variable;
	% fail if it doesn't have one
:- pred size_varset__search_name(size_varset, size_var, string).
:- mode size_varset__search_name(in, in, out) is semidet.



:- pred size_varset__init_var_supply(size_var_supply).
:- mode size_varset__init_var_supply(out) is det.
:- mode size_varset__init_var_supply(in) is semidet. % implied
%       size_varset__init_var_supply(VarSupply) :
%               returns a fresh var_supply for producing fresh variables.

:- pred size_varset__create_var(size_var_supply, size_var, size_var_supply).
:- mode size_varset__create_var(in, out, out) is det.
%       size_varset__create_var(VarSupply0, Variable, VarSupply) :
%               create a fresh variable (size_var) and return the
%               updated var_supply.

:- pred size_varset__size_var_to_int(size_var, int).
:- mode size_varset__size_var_to_int(in, out) is det.
%               Convert a variable to an int.
%               Different variables map to different ints.
%               Other than that, the mapping is unspecified.

/*

	% bind a value to a size_variable
	% (will overwrite any existing binding).
:- pred size_varset__bind_var(size_varset, size_var, term, size_varset).
:- mode size_varset__bind_var(in, in, in, out) is det.

	% bind a set of terms to a set of size_variables.
:- pred size_varset__bind_vars(size_varset, substitution, size_varset).
:- mode size_varset__bind_vars(in, in, out) is det.

	% lookup the value of a size_variable
:- pred size_varset__search_var(size_varset, size_var, term).
:- mode size_varset__search_var(in, in, out) is semidet.

	% get the bindings for all the bound size_variables.
:- pred size_varset__lookup_vars(size_varset, substitution).
:- mode size_varset__lookup_vars(in, out) is det.

	% Combine two different size_varsets, renaming apart:
	% size_varset__merge(VarSet0, NewVarSet, Terms0, VarSet, Terms) is
	% true iff VarSet is the size_varset that results from joining
	% VarSet0 to a suitably renamed version of NewVarSet,
	% and Terms is Terms0 renamed accordingly.
	% (Any bindings in NewVarSet are ignored.)

%:- pred size_varset__merge(size_varset, size_varset, list(term), size_varset, list(term)).
%:- mode size_varset__merge(in, in, in, out, out) is det.

	% As above, except return the substitution directly
	% rather than applying it to a list of terms.

%:- pred size_varset__merge_subst(size_varset, size_varset, size_varset, substitution).
%:- mode size_varset__merge_subst(in, in, out, out) is det.

	% get the bindings for all the bound size_variables.
:- pred size_varset__get_bindings(size_varset, substitution).
:- mode size_varset__get_bindings(in, out) is det.

	% set the bindings for all the bound size_variables.
:- pred size_varset__set_bindings(size_varset, substitution, size_varset).
:- mode size_varset__set_bindings(in, in, out) is det.

	% Create a map from names to size_variables.
	% Each name is mapped to only one size_variable, even if a name is
	% shared by more than one size_variable. Therefore this predicate
	% is only really useful if it is already known that no two
	% size_variables share the same name.
:- pred size_varset__create_name_var_map(size_varset, map(string, size_var)).
:- mode size_varset__create_name_var_map(in, out) is det.

	% Return an association list giving the name of each size_variable.
	% Every size_variable has an entry in the returned association list,
	% even if it shares its name with another size_variable.
:- pred size_varset__var_name_list(size_varset, assoc_list(size_var, string)).
:- mode size_varset__var_name_list(in, out) is det.

	% Given a list of size_variable and size_varset in which some size_variables have
	% no name but some other size_variables may have the same name,
	% return another size_varset in which every size_variable has a unique name.
	% If necessary, names will have suffixes added on the end;
	% the second argument gives the suffix to use.
:- pred size_varset__ensure_unique_names(list(size_var), string, size_varset, size_varset).
:- mode size_varset__ensure_unique_names(in, in, in, out) is det.

	% Given a size_varset and a set of size_variables, remove the names
	% and values of any other size_variables stored in the size_varset.
:- pred size_varset__select(size_varset, set(size_var), size_varset).
:- mode size_varset__select(in, in, out) is det.

	% Given a size_varset and a list of size_variables, construct a new size_varset
	% containing one size_variable for each one in the list (and no others).
	% Also return a substitution mapping the selected size_variables in the
	% original size_varset into size_variables in the new size_varset. The relative
	% ordering of size_variables in the original size_varset is maintained.
:- pred size_varset__squash(size_varset, list(size_var), size_varset, map(size_var, size_var)).
:- mode size_varset__squash(in, in, out, out) is det.

*/
%-----------------------------------------------------------------------------%

:- implementation.
:- import_module int, list, map, std_util, assoc_list, set, require, string, 
									term.

:- type size_var		==	int.
:- type size_var_supply		== 	int.

:- type size_varset		--->	size_varset(
					size_var_supply,
					map(size_var, string),
					map(size_var, term)
				).

%-----------------------------------------------------------------------------%

size_varset__init(size_varset(VarSupply, Names, Vals)) :-
	size_varset__init_var_supply(VarSupply),
	map__init(Names),
	map__init(Vals).

%-----------------------------------------------------------------------------%

size_varset__is_empty(size_varset(VarSupply, _, _)) :-
	size_varset__init_var_supply(VarSupply).

%-----------------------------------------------------------------------------%

size_varset__new_var(size_varset(MaxId0, Names, Vals), Var,
		size_varset(MaxId, Names, Vals)) :-
	size_varset__create_var(MaxId0, Var, MaxId).

size_varset__new_named_var(size_varset(MaxId0, Names0, Vals), Name, Var,
		size_varset(MaxId, Names, Vals)) :-
	size_varset__create_var(MaxId0, Var, MaxId),
	map__set(Names0, Var, Name, Names).

size_varset__new_vars(Varset0, NumVars, NewVars, Varset) :-
	size_varset__new_vars_2(Varset0, NumVars, [], NewVars, Varset).

:- pred size_varset__new_vars_2(size_varset, int, list(size_var), list(size_var), size_varset).
:- mode size_varset__new_vars_2(in, in, in, out, out) is det.

size_varset__new_vars_2(Varset0, NumVars, NewVars0, NewVars, Varset) :-
	(
		NumVars > 0
	->
		NumVars1 is NumVars - 1,
		size_varset__new_var(Varset0, Var, Varset1),
		size_varset__new_vars_2(Varset1, NumVars1, [Var | NewVars0],
							NewVars, Varset)
	;
		NumVars = 0
	->
		NewVars = NewVars0,
		Varset = Varset0
	;
		error("size_varset__new_vars - invalid call")
	).
		
%-----------------------------------------------------------------------------%

size_varset__delete_var(size_varset(MaxId, Names0, Vals0), Var,
		size_varset(MaxId, Names, Vals)) :-
	map__delete(Names0, Var, Names),
	map__delete(Vals0, Var, Vals).

%-----------------------------------------------------------------------------%

size_varset__delete_vars(Varset, [], Varset).
size_varset__delete_vars(Varset0, [Var | Vars], Varset) :-
	size_varset__delete_var(Varset0, Var, Varset1),
	size_varset__delete_vars(Varset1, Vars, Varset).

%-----------------------------------------------------------------------------%

size_varset__vars(size_varset(MaxId0, _, _), L) :-
	size_varset__init_var_supply(V0),
	size_varset__vars_2(V0, MaxId0, [], L1),
	list__reverse(L1, L).

:- pred size_varset__vars_2(size_var_supply, size_var_supply, list(size_var),
			list(size_var)).
:- mode size_varset__vars_2(in, in, in, out) is det.

size_varset__vars_2(N, Max, L0, L) :-
	(N = Max ->
		L = L0
	;
		size_varset__create_var(N, V, N1),
		size_varset__vars_2(N1, Max, [V|L0], L)
	).

%-----------------------------------------------------------------------------%

size_varset__name_var(VarSet0, Id, Name, VarSet) :-
	VarSet0 = size_varset(MaxId, Names0, Vals),
	map__set(Names0, Id, Name, Names),
	VarSet = size_varset(MaxId, Names, Vals).

%-----------------------------------------------------------------------------%

size_varset__lookup_name(Varset, Id, Name) :-
	( size_varset__search_name(Varset, Id, Name0) ->
		Name = Name0
	;
		size_varset__size_var_to_int(Id, VarNum),
		string__int_to_string(VarNum, NumStr),
		string__append("V_", NumStr, Name)
	).

size_varset__lookup_name(Varset, Id, Prefix, Name) :-
	( size_varset__search_name(Varset, Id, Name0) ->
		Name = Name0
	;
		size_varset__size_var_to_int(Id, VarNum),
		string__int_to_string(VarNum, NumStr),
		string__append(Prefix, NumStr, Name)
	).

size_varset__search_name(size_varset(_, Names, _), Id, Name) :-
	map__search(Names, Id, Name0),
	Name = Name0.
/* This part is useful during debugging when you need to
   be able to distinguish different size_variables with the same name.
	(
		map__member(Names, Id1, Name0),
		Id1 \= Id
	->
		size_varset__size_var_to_int(Id, Int),
		string__format("%s__%d",[s(Name0),i(Int)], Name)
	;
		Name = Name0
	).
*/

%-----------------------------------------------------------------------------%
/*
size_varset__bind_var(size_varset(MaxId, Names, Vals0), Id, Val,
		size_varset(MaxId, Names, Vals)) :-
	map__set(Vals0, Id, Val, Vals).
*/
%-----------------------------------------------------------------------------%
/*
size_varset__bind_vars(Varset0, Subst, Varset) :-
	map__to_assoc_list(Subst, VarTermList),
	size_varset__bind_vars_2(VarTermList, Varset0, Varset).

:- pred size_varset__bind_vars_2(assoc_list(size_var, term), size_varset, size_varset).
:- mode size_varset__bind_vars_2(in, in, out) is det.

size_varset__bind_vars_2([], Varset, Varset).
size_varset__bind_vars_2([V - T | Rest], Varset0, Varset) :-
	size_varset__bind_var(Varset0, V, T, Varset1),
	size_varset__bind_vars_2(Rest, Varset1, Varset).
*/
%-----------------------------------------------------------------------------%
/*
size_varset__search_var(size_varset(_, _, Vals), Id, Val) :-
	map__search(Vals, Id, Val).
*/
%-----------------------------------------------------------------------------%
/*
size_varset__lookup_vars(size_varset(_, _, Subst), Subst).
*/
%-----------------------------------------------------------------------------%
/*
size_varset__get_bindings(size_varset(_, _, Subst), Subst).

size_varset__set_bindings(size_varset(C, N, _), S, size_varset(C, N, S)).
*/
%-----------------------------------------------------------------------------%
/*
	% We scan through the second size_varset, introducing a fresh
	% size_variable into the first size_varset for each size_var in the
	% second, and building up a substitution which maps
	% the size_variables in the second size_varset into the corresponding
	% fresh size_variable in the first size_varset.  We then apply
	% this substition to the list of terms.

%size_varset__merge(VarSet0, VarSet1, TermList0, VarSet, TermList) :-
%	size_varset__merge_subst(VarSet0, VarSet1, VarSet, Subst),
%	term__apply_substitution_to_list(TermList0, Subst, TermList).

size_varset__merge_subst(VarSet0, size_varset(MaxId, Names, Vals),
			VarSet, Subst) :-
	size_varset__init_var_supply(N),
	map__init(Subst0),
	size_varset__merge_subst_2(N, MaxId, Names, Vals, VarSet0, Subst0,
				VarSet, Subst).

:- pred size_varset__merge_subst_2(size_var_supply, size_var_supply, map(size_var, string),
	map(size_var, term), size_varset, substitution, size_varset, substitution).
:- mode size_varset__merge_subst_2(in, in, in, in, in, in, out, out) is det.

size_varset__merge_subst_2(N, Max, Names, Vals, VarSet0, Subst0, VarSet, Subst) :-
	( N = Max ->
		VarSet = VarSet0,
		Subst0 = Subst
	;
		size_varset__new_var(VarSet0, VarId, VarSet1),
		size_varset__create_var(N, VarN, N1),
		(
			map__search(Names, VarN, Name)
		->
			size_varset__name_var(VarSet1, VarId, Name, VarSet2)
		;
			VarSet2 = VarSet1
		),
		map__set(Subst0, VarN, term__variable(VarId), Subst1),
		size_varset__merge_subst_2(N1, Max, Names, Vals, VarSet2, Subst1,
				VarSet, Subst)
	).
*/
%-----------------------------------------------------------------------------%
/*
size_varset__create_name_var_map(size_varset(_, VarNameIndex, _), NameVarIndex) :-
	map__keys(VarNameIndex, Vars),
	map__values(VarNameIndex, Names),
	map__from_corresponding_lists(Names, Vars, NameVarIndex).

%-----------------------------------------------------------------------------%
/*
size_varset__var_name_list(size_varset(_, VarNameIndex, _), VarNameList) :-
	map__to_assoc_list(VarNameIndex, VarNameList).
*/
%-----------------------------------------------------------------------------%
/*
size_varset__ensure_unique_names(AllVars, Suffix,
		size_varset(Supply, VarNameMap0, Values),
		size_varset(Supply, VarNameMap, Values)) :-
	set__init(UsedNames),
	map__init(VarNameMap1),
	size_varset__ensure_unique_names_2(AllVars, Suffix, UsedNames, VarNameMap0,
		VarNameMap1, VarNameMap).

:- pred size_varset__ensure_unique_names_2(list(size_var), string, set(string),
	map(size_var, string), map(size_var, string), map(size_var, string)).
:- mode size_varset__ensure_unique_names_2(in, in, in, in, in, out) is det.

size_varset__ensure_unique_names_2([], _, _, _, VarNameMap, VarNameMap).
size_varset__ensure_unique_names_2([Var | Vars], Suffix, UsedNames0,
		OldVarNameMap, VarNameMap0, VarNameMap) :-
	( map__search(OldVarNameMap, Var, OldName) ->
		( set__member(OldName, UsedNames0) ->
			size_varset__size_var_to_int(Var, VarNum),
			string__int_to_string(VarNum, NumStr),
			string__append("_", NumStr, NumSuffix),
			string__append(OldName, NumSuffix, TrialName)
		;
			TrialName = OldName
		)
	;
		size_varset__size_var_to_int(Var, VarNum),
		string__int_to_string(VarNum, NumStr),
		string__append("Var_", NumStr, TrialName)
	),
	size_varset__ensure_unique_names_3(TrialName, Suffix, UsedNames0, FinalName),
	set__insert(UsedNames0, FinalName, UsedNames1),
	map__det_insert(VarNameMap0, Var, FinalName, VarNameMap1),
	size_varset__ensure_unique_names_2(Vars, Suffix, UsedNames1, OldVarNameMap,
		VarNameMap1, VarNameMap).

:- pred size_varset__ensure_unique_names_3(string, string, set(string), string).
:- mode size_varset__ensure_unique_names_3(in, in, in, out) is det.

size_varset__ensure_unique_names_3(Trial0, Suffix, UsedNames, Final) :-
	( set__member(Trial0, UsedNames) ->
		string__append(Trial0, Suffix, Trial1),
		size_varset__ensure_unique_names_3(Trial1, Suffix, UsedNames, Final)
	;
		Final = Trial0
	).
*/
%-----------------------------------------------------------------------------%
/*
size_varset__select(size_varset(Supply, VarNameMap0, Values0), Vars,
		size_varset(Supply, VarNameMap, Values)) :-
	map__select(VarNameMap0, Vars, VarNameMap),
	map__select(Values0, Vars, Values).
*/
%-----------------------------------------------------------------------------%
/*
size_varset__squash(OldVarSet, KeptVars, NewVarSet, Subst) :-
	%
	% Create a new size_varset with the same number of size_variables. 
	%
	list__length(KeptVars, NumVars),
	size_varset__init(NewVarSet0),
	size_varset__new_vars(NewVarSet0, NumVars, 
		NewVars0, NewVarSet1),
	%
	% We need to sort the fresh size_variables, to
	% ensure that the substitution that we create below
	% does not alter the relative ordering of the size_variables
	%
	list__sort(NewVars0, NewVars),

	%
	% Copy the size_variable names across from the old
	% size_varset to the new size_varset.
	%
	size_varset__var_name_list(OldVarSet, VarNames),
	map__from_corresponding_lists(KeptVars, NewVars, Subst),
	copy_var_names(VarNames, Subst, NewVarSet1, NewVarSet).

:- pred copy_var_names(assoc_list(size_var, string), map(size_var, size_var), size_varset, size_varset).
:- mode copy_var_names(in, in, in, out) is det.

copy_var_names([], _Subst, NewVarSet, NewVarSet).
copy_var_names([OldVar - Name | Rest], Subst, NewVarSet0, NewVarSet) :-
	( map__search(Subst, OldVar, NewVar) ->
		size_varset__name_var(NewVarSet0, NewVar, Name, NewVarSet1)
	;
		NewVarSet1 = NewVarSet0
	),
	copy_var_names(Rest, Subst, NewVarSet1, NewVarSet).
*/
%-----------------------------------------------------------------------------%

% These are copies of predicates from term.m:

        % create a new supply of variables
size_varset__init_var_supply(0).

	% We number variables using sequential numbers,

size_varset__create_var(VarSupply0, VarSupply, VarSupply) :-
	VarSupply is VarSupply0 + 1.

size_varset__size_var_to_int(Var, Var).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%


