%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_datastruct: defines the datastruct type used within 
% 	possible alias analysis, and used during structure reuse analysis. 
% 	A datastruct essentially designates a selector path within
%	a program variable. 
% main author: nancy

% notes: 
% 1. contains some code which is common to Wim's BTA analysis. At some
%    point this should be really shared. It is not the case at this
%    moment. 
% 2. _partially instantiated datastructures_ : the day they'll be 
%    introduced, a couple of things will have to be changed.

:- module possible_alias__pa_datastruct.

:- interface.

:- import_module hlds__hlds_data.
:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module parse_tree__prog_data.

:- import_module map, term, std_util.

%-------------------------------------------------------------------%
%-- exported types

% Type-definition has become public and is moved to prog_data.
% :- type datastruct.

%-------------------------------------------------------------------%
%-- exported predicates

%-------------------------------------------------------------------%
% predicates for the datastruct type
%-------------------------------------------------------------------%
	% init(Var, D)
	% Create an initial top-datastruct for variable Var.
:- pred init(prog_var::in, datastruct::out) is det.
:- func init(prog_var) = datastruct. 

	% Initialise a datastructure by its variable and selector. 
:- pred init(prog_var::in, selector::in, datastruct::out) is det.

	% init(Var, Cons, Index, D)
	% Create an initial datastruct Var^(Cons,Index), thus a data structure
	% with a selector consisting of only one unit selector, namely the one
	% identified by the constructor and index within that constructor. 
:- pred init(prog_var::in, cons_id::in, int::in, datastruct::out) is det.

	% Extend the given datastructure with an additional path.
:- pred termshift(datastruct::in, selector::in, datastruct::out) is det. 

	% less_or_equal(LongerData,ShorterData,Selector)
	% Check whether by extending the ShorterData with some selector
	% Selector one can obtain LongerData. 
	% If the datastructs concern different variables, fail right away.
:- pred less_or_equal(module_info::in, proc_info::in, datastruct::in,
		datastruct::in, selector::out) is semidet.

	% Check whether the two given datastructs are related to the
	% same variable or not. 
:- pred same_vars(datastruct::in, datastruct::in) is semidet.

	% Check whether the given datastructs are identical or not.
:- pred equal(datastruct::in, datastruct::in) is semidet.

	% Rename the variable of the given datastruct.
:- pred rename(map(prog_var,prog_var)::in, 
		maybe(substitution(tvar_type))::in, 
		datastruct::in, datastruct::out) is det.

:- pred normalize_wti(module_info::in, proc_info::in, 
		datastruct::in, datastruct::out) is det.

:- pred apply_widening(module_info::in, proc_info::in, datastruct::in, 
			datastruct::out) is det.
:- func apply_widening(module_info, proc_info, datastruct) = datastruct.

:- func type_of_node(module_info, proc_info, datastruct) = (type). 
:- func type_of_node_with_vartypes(module_info, map(prog_var, type), 
						datastruct) = (type). 

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
:- implementation.

:- import_module check_hlds__type_util.
:- import_module parse_tree__prog_io_pasr.
:- import_module possible_alias__pa_selector.

:- import_module string, varset, require, list.

% :- type datastruct ---> cel(prog_var, pa_selector__selector).

% get_var(cel(Var, _Sel), Var).
% var(cel(Var, _Sel)) = Var. 
% get_selector(cel(_Var, Sel), Sel).
% selector(cel(_Var, Sel)) = Sel.


rename(ProgVarMap, MaybeSubst, Data0, Data) :-
	Data0 = selected_cel(Var0, Sel0),
	map__lookup(ProgVarMap, Var0, Var),
	pa_selector__maybe_rename_types(MaybeSubst, Sel0, Sel), 
	Data = selected_cel(Var, Sel).

equal(D1, D2):- D1 = D2.

same_vars(D1, D2):- 
	D1^sc_var = D2^sc_var.

less_or_equal(ModuleInfo, ProcInfo, D1,D2, EXT):-
	same_vars(D1,D2),
	proc_info_vartypes(ProcInfo, VarTypes), 
	map__lookup(VarTypes, D1^sc_var, ProgVarType), 
	(
		equal(D1,D2)
	->
		pa_selector__init(EXT)
	;
		S1 = D1^sc_selector, 
		S2 = D2^sc_selector, 
		pa_selector__less_or_equal(ModuleInfo,S1,S2,ProgVarType,EXT)
	).

termshift(Din, S, Dout):-
	Din = selected_cel(V,Sin),
	pa_selector__termshift(Sin,S,Sout),
	Dout = selected_cel(V,Sout).

init(V, CONS, INDEX, Dout) :-
	pa_selector__init(CONS,INDEX, SEL),
	Dout = selected_cel(V,SEL).

init(V, Dout) :-
	SEL = [],
	Dout = selected_cel(V, SEL).
init(V) = D :- init(V, D).

init(V, Sel, Dout) :- 
	Dout = selected_cel(V, Sel). 

normalize_wti(HLDS, ProcInfo, Din, Dout):-
	proc_info_vartypes(ProcInfo, VarTypes), 
	normalize_wti_2(HLDS, VarTypes, Din, Dout). 

	% normalize with type information
:- pred normalize_wti_2(module_info, vartypes, 
		datastruct, datastruct).
:- mode normalize_wti_2(in, in, in, out) is det.

normalize_wti_2(HLDS, VarTypes, D0, D):-
	D0 = selected_cel(ProgVar, SEL0), 
	map__lookup(VarTypes, ProgVar, VarType),
	pa_selector__normalize_wti(HLDS, VarType, SEL0, SEL),
	D = selected_cel(ProgVar, SEL).

apply_widening(ModuleInfo, ProcInfo, D0, D):- 
	D0 = selected_cel(ProgVar, Sel0), 
	proc_info_vartypes(ProcInfo, VarTypes), 
	map__lookup(VarTypes, ProgVar, ProgVarType), 
	pa_selector__apply_widening(ModuleInfo, ProgVarType, Sel0, Sel), 
	D = selected_cel(ProgVar, Sel). 

apply_widening(ModuleInfo, ProcInfo, D0) = D :- 
	apply_widening(ModuleInfo, ProcInfo, D0, D).

type_of_node(ModuleInfo, ProcInfo, Data) = Type :- 
	proc_info_vartypes(ProcInfo, VarTypes), 
	Type = type_of_node_with_vartypes(ModuleInfo, VarTypes, Data). 

type_of_node_with_vartypes(ModuleInfo, VarTypes, Data) = Type :- 
	Data = selected_cel(ProgVar, Sel), 
	map__lookup(VarTypes, ProgVar, ProgVarType), 
	Type = pa_selector__type_of_node(ModuleInfo, ProgVarType, Sel). 


