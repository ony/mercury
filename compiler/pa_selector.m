%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_selector: defines the selectors as they are used within 
%	   	      the possible alias analysis.
% main author: nancy

% notes: 
% 1. this code is quite similar to (and in fact based on) the code Wim
%    wrote for his BTA where he also uses the concept of a selector. At
%    some point this code could be really shared by both analysis. 
% 2. _partially instantiated datastructures_ : the day they'll be 
%    introduced, a couple of things will have to be changed.

:- module pa_selector.

:- interface.

%-------------------------------------------------------------------%
%-- import_module 

% library modules
:- import_module list, int, io, term.

% XXX parent modules
:- import_module hlds, parse_tree.
% compiler modules
:- import_module hlds__hlds_data, hlds__hlds_module.
:- import_module parse_tree__prog_data.


%-------------------------------------------------------------------%
%-- exported types

:- type selector == list(unit_sel).
:- type unit_sel ---> 
		us(hlds_data__cons_id, int) ;  % normal selector
		ts(prog_data__type).		 % type selector
			

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%


	% create an initial top selector.
:- pred init(selector::out) is det.

	% create an initial selector with given constructor and index.
:- pred init(cons_id::in, int::in, selector::out) is det.

:- pred from_types(list(type)::in, selector::out) is det.

	% check whether the selector is a top-selector.
:- pred top(selector::in) is semidet.

	% select_first_part(InputSelector, Head_unit_selector, Tail).
	% Select the first unit selector from the given selector, 
	% and return also the remainders. 
	% The predicate produces a software error when the input
	% selector is a top-selector.
:- pred select_first_part(selector, unit_sel, selector).
:- mode select_first_part(in, out, out) is det.

	% termshift(InputSelector, NewExtension, ResultingSelector).
	% Extend the given selector with a new extension (unit selector). 
:- pred unit_termshift(selector, unit_sel, selector).
:- mode unit_termshift(in, in, out) is det.

:- pred termshift(selector, selector, selector).
:- mode termshift(in, in, out) is det.

	% less_or_equal(HLDS, S1, S2, T, EXT):
	% Find out whether selector S1 of a variable of type T is
	% less or equal to another selector S2 belonging to the same
	% variable of type T. If so, return the extension such that
	% S1 == S2.EXT
:- pred less_or_equal(module_info::in, selector::in, selector::in, 
		(type)::in, selector::out) is semidet.

:- pred rename_types(term__substitution(tvar_type)::in, 
		selector::in, selector::out) is det.

:- pred print(selector::in, tvarset::in, 
		io__state::di, io__state::uo) is det. 
:- pred to_user_declared(selector::in, tvarset::in, string::out) is det. 

:- pred parse_term(term(T), selector).
:- mode parse_term(in, out) is det.

	% normalize with type information
:- pred normalize_wti((type), module_info, selector, selector).
:- mode normalize_wti(in, in, in, out) is det.

	% widening
:- pred apply_widening(module_info::in, (type)::in,
		selector::in, selector::out) is det.

	% Compute the type of the node the selector is pointing to, 
	% given the type of the structure to which the selector belongs. 
:- func type_of_node(module_info, (type), selector) = (type). 

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%

:- implementation.

% library modules
:- import_module require, string, std_util, bool.

% XXX parent modules
:- import_module check_hlds.

% compiler modules
:- import_module parse_tree__mercury_to_mercury, parse_tree__prog_io.
:- import_module parse_tree__prog_out.
:- import_module check_hlds__type_util.
:- import_module hlds__hlds_pred, hlds__hlds_out.


init([]).
init(CONS, INDEX, SEL):-
	US = us(CONS, INDEX),
	SEL = [US].
from_types(Types, Selector):- 
	list__map(
		pred(T::in, US::out) is det :- 
			US = ts(T),
		Types,
		Selector). 	
		

top([]).

select_first_part(SEL0, US, SEL):-
	(
		SEL0 = [ F | R ]
	->
		US = F, SEL = R
	;
		error("(pa_selector): trying to split empty selector!")
	).

unit_termshift(S0, US, S):-
	termshift(S0,[US],S).
termshift(S1,S2,S):- list__append(S1,S2,S).

	% less_or_equal(S1, S2, EXT).
	% Predicate holds when S1 is less than or equal to S2 ("is 
	% subsumed by"), i.e. S1 can be selected by extending S2 with
	% the extension EXT (output).
	% PRECONDITION: the selectors do not contain any type-selectors. 
:- pred less_or_equal(selector, selector, selector).
:- mode less_or_equal(in, in, out) is semidet.

less_or_equal(S1, S2, EXT) :- 
	list__append(S2, EXT , S1). 


rename_types(Subst, Sel0, Sel):- 
	list__map(unit_selector_rename_types(Subst), Sel0, Sel).

:- pred unit_selector_rename_types(term__substitution(tvar_type)::in,
		unit_sel::in, unit_sel::out) is det.

unit_selector_rename_types(Subst, US0, US) :- 
	(
		US0 = us(_,_),
		US = US0
	;
		US0 = ts(Type0), 
		term__apply_substitution(Type0, Subst, Type), 
		US = ts(Type)
	).
	
print(Selector, ProgVarSet) -->
	io__write_string("["),
	io__write_list(Selector, ",", print_unit_selector(ProgVarSet)),
	io__write_string("]").

:- pred print_unit_selector(tvarset, unit_sel, io__state, io__state).
:- mode print_unit_selector(in, in, di, uo) is det.

print_unit_selector(_ProgVarSet, us(Cons, Index)) -->
	{ hlds_data__cons_id_arity(Cons, Arity) },
	io__write_string("sel("),
	mercury_output_cons_id(Cons, needs_brackets),
	io__write_string(","),
	io__write_int(Arity),
	io__write_string(","),
	io__write_int(Index),
	io__write_string(")").
print_unit_selector(ProgVarSet, ts(Type)) --> 
	io__write_string("typesel("), 
	mercury_output_term(Type, ProgVarSet, bool__no), 
	io__write_string(")").

to_user_declared(Selector, TVarSet, String):- 
	(
		Selector = []
	-> 
		String = "[]"
	; 
		to_user_declared_2(Selector, TVarSet, String2), 
		string__append_list(["[", String2, "]"], String)
	). 

:- pred to_user_declared_2(selector::in, tvarset::in, string::out) is det.

to_user_declared_2([], _, "").
to_user_declared_2([First | Rest], TVarSet, String):- 
	us_to_user_declared(First, TVarSet, FirstString), 
	(
		Rest = []
	->
		String = FirstString
	;
		to_user_declared_2(Rest, TVarSet, RestString), 
		string__append_list([FirstString, ", ", RestString], 
			String)
	). 

:- pred us_to_user_declared(unit_sel::in, tvarset::in, string::out) is det.
us_to_user_declared(us(_,_), _, _):- 
	require__error("(pa_selector) us_to_user_declared: only type-selectors are allowed in user-alias-declaration.").
us_to_user_declared(ts(Type), TVarSet, 
		mercury_type_to_string(TVarSet, Type)). 

parse_term(TERM, SEL):- 
	(
		TERM = term__functor(term__atom(CONS), Args, _)
	->
		(
			CONS = "[|]",
			Args = [ First , Rest ]
		->
			parse_unit_selector(First, US),
			parse_term(Rest, SELrest),
			SEL = [ US | SELrest ]
		;
			SEL = []
		)
	;
		error("(pa_selector) parse_term: term not a functor")
	).

:- pred parse_unit_selector(term(T), unit_sel).
:- mode parse_unit_selector(in, out) is det.

parse_unit_selector(TERM, US):- 
   (
      TERM = term__functor(term__atom(CONS), Args, _)
   ->
      (
         CONS = "sel",
         Args = [ CONS_TERM, ARITY_TERM, POS_TERM ]
      ->
         (
            prog_io__sym_name_and_args(CONS_TERM, ConsID_SN, ConsID_ARGS),
            ConsID_ARGS = [],
	    ARITY_TERM = term__functor(term__integer(Arity), _, _),
            POS_TERM = term__functor(term__integer(Pos), _, _)
         ->
	    ConsID = cons(ConsID_SN, Arity),
	    US = us(ConsID, Pos)
	 ;
	    CONS_TERM = term__functor(term__integer(X), _, _)
	 ->
	    ConsID = int_const(X), 
	    US = us(ConsID, 0)
	 ;
	    CONS_TERM = term__functor(term__float(X), _, _)
	 ->
	    ConsID = float_const(X),
	    US = us(ConsID, 0)
	 ;
	    CONS_TERM = term__functor(term__string(S), _, _)
	 ->
	    ConsID = string_const(S),
	    US = us(ConsID, 0)
	 ;
	    error("(pa_selector) parse_unit_selector: unknown cons_id in unit selector")
	 )
      ; 
	 
         CONS = "typesel",
	 Args = [ TypeSelectorTerm ]
      ->
 	 term__coerce(TypeSelectorTerm, TypeSelector), 
	 US = ts(TypeSelector)
      ;
	 error("(pa_selector) parse_unit_selector: top constructor should be sel/3 or typesel/1.")
      )
   ;
      error("(pa_selector) parse_unit_selector: term not a functor")
   ).


normalize_wti(VarType, HLDS, SEL0, SEL):-
	(
		type_util__is_introduced_type_info_type(VarType)
	->
		SEL = SEL0
	; 
		branch_map_init(B0), 
		init(TOP),
		branch_map_insert(VarType, TOP, B0, B1),
		normalize_wti_2(VarType, HLDS, B1, TOP, SEL0, SEL)
	).

:- pred normalize_wti_2(type, module_info, branch_map, 
				selector, selector, selector).
:- mode normalize_wti_2(in, in, in, in, in, out) is det.

normalize_wti_2(VarType, HLDS, B0, Acc0, SEL0, SEL):-
	(
		SEL0 = [ US | SELR ]
	->
		type_util__classify_type(VarType, HLDS, Class),
		(
			Class = user_type
		->
			% switch on the kind of selector, unit selector
			% or type selector. 
			(
			    (
				US = us(CONS, INDEX),
				type_util__get_cons_id_non_existential_arg_types(HLDS, 
					VarType, CONS, ArgTypes),
				(
					list__index1(ArgTypes, INDEX, SubType)
				->
					CType = SubType
				;
					error(index_error_message(HLDS, 
						VarType, CONS, INDEX))
				)
			    ;
				US = ts(CType)
			    )
			->
				(
					branch_map_search(B0, CType,
						BSel)
				->
					normalize_wti_2(CType, HLDS,
						B0, BSel, SELR, SEL)
				;
					unit_termshift(Acc0, US, 
						Acc1),
					branch_map_insert(CType, 
						Acc1, B0, B1),
					normalize_wti_2(CType, HLDS, 
						B1, Acc1, SELR, SEL)
				)
			;
				% existentially typed functor.
				append(Acc0, SEL0, SEL)
			)
		;
			% if it's not a user type, SELR will be empty
			% anyhow, and normalization stops.
			% Resulting selector = accumulator.sel0
			% selector_add_us(Acc0, US, SEL)
			append(Acc0,SEL0,SEL)

		)
	;
		% SEL0 = []		
		SEL = Acc0
	).

:- func index_error_message(module_info, (type), cons_id, int) = string. 
index_error_message(HLDS, VarType, CONS, INDEX) = Msg :- 
	get_type_defn(HLDS,VarType,TypeDefn),

	(
		type_util__type_to_ctor_and_args(VarType, TypeCTor0, _)
	->
		TypeCTor = TypeCTor0
	; 
		error("(pa_selector) index_error_message: type is not a non-var type.")
	),
	
	type_util__type_ctor_module(HLDS, TypeCTor, ModuleName),	
	type_util__type_ctor_name(HLDS, TypeCTor, TypeName),
	type_util__type_ctor_arity(HLDS, TypeCTor, Arity),

	hlds_data__get_type_defn_status(TypeDefn, TypeImportStatus),
	hlds_data__get_type_defn_body(TypeDefn, TypeBody), 

	hlds_type_body_to_minimal_string(TypeBody, BodyString),
	hlds_pred__import_status_to_minimal_string(TypeImportStatus,
		StatusString),

	prog_out__sym_name_to_string(ModuleName, "__", SModuleName),	
	hlds_out__cons_id_to_string(CONS,SCONS),
	string__int_to_string(INDEX,SINDEX),
	string__int_to_string(Arity, SArity),
	string__append_list([
		"\n(pa_selector) normalize_wti_2: index not found.\n",
		"(pa)              type is ", SModuleName, "::",TypeName, "/",
				SArity, " -> ", SCONS, " -- ", SINDEX, "\n",
		"(pa)              (", BodyString, " and ", 
					StatusString, ").\n"], 
		Msg).
	

:- pred get_type_defn(module_info,(type),hlds_type_defn).
:- mode get_type_defn(in,in,out) is det.

get_type_defn(HLDS,VarType,TypeDefn):-
	(
		type_to_ctor_and_args(VarType, TypeCTor, _TypeArgs),
		module_info_types(HLDS,Types),
		map__lookup(Types,TypeCTor,TypeDefn0)
	->
		TypeDefn = TypeDefn0
	;
		error("(pa_selector) get_type_defn: no type definition")
	).

:- pred hlds_type_body_to_minimal_string(hlds_type_body, string).
:- mode hlds_type_body_to_minimal_string(in,out) is det.

hlds_type_body_to_minimal_string(du_type(_,_,_,_,_), "du_type").
hlds_type_body_to_minimal_string(eqv_type(_), "eqv_type").
hlds_type_body_to_minimal_string(abstract_type, "abstract_type").
hlds_type_body_to_minimal_string(foreign_type(_), "foreign_type").



%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
% BRANCH_MAP : copy/pasted from wimvh/bta_reduce.m
%-------------------------------------------------------------------%

:- import_module assoc_list, map.

:- type branch_map == assoc_list(type, selector).

:- pred branch_map_init(branch_map).
:- mode branch_map_init(out) is det.

:- pred branch_map_insert(type, selector, branch_map, branch_map).
:- mode branch_map_insert(in, in, in, out) is det.
        
:- pred branch_map_search(branch_map, type, selector).
:- mode branch_map_search(in, in, out) is semidet.

branch_map_init([]).

branch_map_insert(Type, SelPart, Map1, [(Type - SelPart) | Map1]).

branch_map_search([ (T1 - S1) | Ms ], T2, S):-
        map__init(Empty),
                % The two types are considered equal if they
		% unify
                % under an empty substitution
        (
		type_unify(T1, T2, [], Empty, Subst), 
		map__is_empty(Subst)
	->
                S = S1
	;
	        branch_map_search(Ms, T2, S)
	).


%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
% additional predicates
%-------------------------------------------------------------------%

	% split_upto_type_selector(Sin, S1, TS, S2): 
	%	this predicate succeeds if there exists a typeselector
	% 	TS, such that Sin is equivalent to append(S1, [TS | S2])
	% 	and S1 contains no other type selector. It fails otherwise. 
:- pred split_upto_type_selector(selector::in, selector::out, 
		unit_sel::out,
		selector::out) is semidet.

split_upto_type_selector(Sin, S1, TS, S2):-
	split_upto_type_selector_acc(Sin, [], S1, TS, S2). 

:- pred split_upto_type_selector_acc(selector::in, selector::in, 
		selector::out, unit_sel::out, selector::out) is semidet.
split_upto_type_selector_acc([ US | SEL ], ACC, S1, TS, S2):-
	(
		US = ts(_)
	->
		S1 = ACC, 
		TS = US, 
		S2 = SEL
	; 
		append(ACC, [US], ACC2),
		split_upto_type_selector_acc(SEL, ACC2, S1, TS, S2)
	). 


less_or_equal(HLDS, S1, S2, MainType, EXT):- 
	normalize_wti(MainType, HLDS, S1, NormS1), 
	normalize_wti(MainType, HLDS, S2, NormS2), 
	less_or_equal_2(HLDS, NormS1, NormS2, MainType, EXT). 

:- pred less_or_equal_2(module_info::in, selector::in, selector::in, 
		(type)::in, selector::out) is semidet.

less_or_equal_2(HLDS, S1, S2, MainType, EXT):- 
	(
		split_upto_type_selector(S2, S2_part1, TS, S2_part2),
		TS = ts(SubType)
	->
		(

			less_or_equal_2(HLDS, S1, S2_part1, MainType, Rest)
			% append(S2_part1, Rest, S1) % walk past S2_part1
						% S1 = S2_part1.Rest
		->
			% and now the type-testing part... 
			% can be formulated as: starting from S2_part1,
			% does the remainder of the path Rest lead through
			% some node of type TSType ? 
			get_type_of_node(HLDS, MainType, S2_part1, NodeType), 
				% from NodeType, to TS
			type_on_path(HLDS, NodeType, SubType, Rest, Remainder),
			less_or_equal_2(HLDS, Remainder, S2_part2, SubType, EXT)
		;
			fail	% the walks do not correspond
		)
	; 	
		% In the case that the second selector S2 has no type-
		% selectors, the first one S1 can still be less or
		% equal to the second one if all the selectors of S2
		% correspond exactly to the first steps of S1, 
		% so just: S1 = S2.ext, or rather: 
		% less_or_equal(S2, S1, Extension) (the simple case)
			less_or_equal(S1, S2, EXT)
	). 

apply_widening(ModuleInfo, MainType, Selector0, Selector) :-
	(
		Selector0 = []
	-> 
		Selector = Selector0
	; 
		get_type_of_node(ModuleInfo, MainType, Selector0, SubType), 
		Selector = [ ts(SubType) ]
	).

type_of_node(ModuleInfo, StartType, Selector) = SubType :-
	get_type_of_node(ModuleInfo, StartType, Selector, SubType). 

	% get_type_of_node(ModuleInfo, StartType, Selector, SubType)
	% determines the type SybType of the node obtained by traversing
	% the StartType using the path Selector. 
:- pred get_type_of_node(module_info::in, (type)::in, selector::in, 
		(type)::out) is det.
get_type_of_node(ModuleInfo, StartType, Selector, SubType):-
	(
		Selector = [ US | RestSelector ]
	->
		(
			US = us(CONS_ID, CHOICE),
			select_subtype(ModuleInfo, StartType, CONS_ID, 
				CHOICE, SubType0) 
		; 
			US = ts(SubType0)
		),
		get_type_of_node(ModuleInfo, SubType0, 
				RestSelector, SubType)	
	;
		SubType = StartType
	).

	% select_subtype(ModuleInfo, Type, ConsID, Position, SubType):
	% select the subtype of a type Type, selecting ConsId's position
	% Position. Position counts starting from 1 (and not 0). 
	% Predicate aborts if subtype cannot be determined. 
:- pred select_subtype(module_info::in, (type)::in, 
		cons_id::in, int::in, (type)::out) is det.
select_subtype(ModuleInfo, Type, ConsID, Choice, SubType) :-
	(
		type_util__get_cons_id_non_existential_arg_types(ModuleInfo, 
			Type, ConsID, ArgTypes)
	->
		(
			list__index1(ArgTypes, Choice, SubType0)
		->
			SubType = SubType0
		;
			require__error("(pa_selector) get_type_of_node: selection of subtype failed.")
		)
	;
		require__error("(pa_selector) get_type_of_node: existential type encountered.")
	).


	% type_on_path(ModuleInfo, FromType, ToType, Path, Remainder):
	% this predicate verifies that the path Path starting from 
	% FromType passes the type ToType. Remainder is the remainder
	% of the selector. 
	% The Path may contain type-selectors. 
	% XXX this predicate should be nondet as Path might lead through
	% different nodes of type ToType, each yielding a different
	% Remainder. 
:- pred type_on_path(module_info::in, (type)::in, (type)::in, 
		selector::in, selector::out) is semidet.

type_on_path(ModuleInfo, FromType, ToType, Path, RemainderPath) :-
	% require at least one step!
	% Why? The meaning of a type-selector is that it is a shortcut
	% notation of any non-zero selector which selects a node of
	% the type described in the type-selector. 
	type_on_path_2(first, ModuleInfo, FromType, 
			ToType, Path, RemainderPath).

:- type step ---> first ; subsequent. 
:- pred type_on_path_2(step::in, module_info::in, (type)::in, (type)::in, 
		selector::in, selector::out) is semidet.

type_on_path_2(Step, ModuleInfo, FromType, ToType, Path, RemainderPath) :- 
	(
		FromType = ToType, 
		Step = subsequent	
	->
		RemainderPath = Path
	; 
		Path = [ US | Rest ],
		(
			US = ts(SubType),
			(
				SubType = ToType
			->
				RemainderPath = Rest
			;
				type_on_path_2(subsequent, ModuleInfo, 
						SubType, ToType, 
						Rest, RemainderPath)
			)
		;
			US = us(CONS_ID, CHOICE), 
			select_subtype(ModuleInfo, FromType, CONS_ID, 
				CHOICE, SubType),
			(
				SubType = ToType
			->
				RemainderPath = Rest
			;
				type_on_path_2(subsequent, 
					ModuleInfo, SubType, ToType, 
					Rest, RemainderPath)
			)
		)
	).



	

