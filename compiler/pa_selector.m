%-----------------------------------------------------------------------------%
% Copyright (C) 1996-2000 The University of Melbourne.
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

% compiler modules
:- import_module hlds_data, prog_data, hlds_module.


%-------------------------------------------------------------------%
%-- exported types

:- type selector == list(unit_sel).
:- type unit_sel ---> us( hlds_data__cons_id, int ).

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%


	% create an initial top selector.
:- pred init(selector::out) is det.

	% create an initial selector with given constructor and index.
:- pred init(cons_id::in, int::in, selector::out) is det.

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

	% less_or_equal(S1, S2, EXT).
	% Predicate holds when S1 is less than or equal to S2 ("is 
	% subsumed by"), i.e. S1 can be selected by extending S2 with
	% the extension EXT (output).
:- pred less_or_equal(selector, selector, selector).
:- mode less_or_equal(in, in, out) is semidet.

:- pred print( selector, io__state, io__state).
:- mode print( in, di, uo) is det.

:- pred parse_term( term(T), selector).
:- mode parse_term( in, out ) is det.

	% normalize with type information
:- pred normalize_wti( (type), module_info, selector, selector).
:- mode normalize_wti( in, in, in, out) is det.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%

:- implementation.

% library modules
:- import_module require, string, std_util.

% compiler modules
:- import_module mercury_to_mercury, prog_io, type_util.
:- import_module hlds_pred, prog_out, hlds_out.


init([]).
init(CONS, INDEX, SEL):-
	US = us(CONS, INDEX),
	SEL = [US].

top([]).

select_first_part( SEL0, US, SEL ):-
	(
		SEL0 = [ F | R ]
	->
		US = F, SEL = R
	;
		error("(pa_selector): trying to split empty selector!")
	).

unit_termshift( S0, US, S ):-
	termshift(S0,[US],S).
termshift(S1,S2,S):- list__append(S1,S2,S).

less_or_equal( S1, S2, EXT ) :- 
	list__append(S2, EXT , S1). 

print( SELECTOR ) -->
	io__write_string("["),
	io__write_list(SELECTOR, ",", print_unit_selector),
	io__write_string("]").

:- pred print_unit_selector( unit_sel, io__state, io__state).
:- mode print_unit_selector( in, di, uo) is det.

print_unit_selector( us( CONS, INDEX ) ) -->
	{ hlds_data__cons_id_arity( CONS, ARITY ) },
	io__write_string( "sel("),
	mercury_output_cons_id(CONS, needs_brackets),
	io__write_string( "," ),
	io__write_int( ARITY ),
	io__write_string(","),
	io__write_int(INDEX),
	io__write_string(")").

parse_term( TERM, SEL ):- 
	(
		TERM = term__functor( term__atom(CONS), Args, _)
	->
		(
			CONS = ".",
			Args = [ First , Rest ]
		->
			parse_unit_selector( First, US),
			parse_term( Rest, SELrest ),
			SEL = [ US | SELrest ]
		;
			SEL = []
		)
	;
		error("(pa_selector) parse_term: term not a functor")
	).

:- pred parse_unit_selector( term(T), unit_sel).
:- mode parse_unit_selector( in, out) is det.

parse_unit_selector( TERM, US ):- 
   (
      TERM = term__functor( term__atom(CONS), Args, _)
   ->
      (
         CONS = "sel",
         Args = [ CONS_TERM, ARITY_TERM, POS_TERM ]
      ->
         ( 
            prog_io__sym_name_and_args( CONS_TERM, ConsID_SN, ConsID_ARGS ),
            ConsID_ARGS = [],
	    ARITY_TERM = term__functor( term__integer( Arity ), _, _),
            POS_TERM = term__functor( term__integer( Pos ), _, _ )
         ->
	    ConsID = cons( ConsID_SN, Arity ),
	    US = us( ConsID, Pos )
	 ;
	    CONS_TERM = term__functor( term__integer( X ), _, _)
	 ->
	    ConsID = int_const( X ), 
	    US = us( ConsID, 0 )
	 ;
	    CONS_TERM = term__functor( term__float( X ), _, _)
	 ->
	    ConsID = float_const( X ),
	    US = us( ConsID, 0)
	 ;
	    CONS_TERM = term__functor( term__string( S ), _, _)
	 ->
	    ConsID = string_const( S ),
	    US = us( ConsID, 0 )
	 ;
	    error("(pa_selector) parse_unit_selector: unknown cons_id in unit selector")
	 )
      ; 
         error("(pa_selector) parse_unit_selector: top constructor should be sel/3")
      )
   ;
      error("(pa_selector) parse_unit_selector: term not a functor")
   ).


normalize_wti( VarType, HLDS, SEL0, SEL ):-
	branch_map_init( B0 ), 
	init( TOP ),
	branch_map_insert( VarType, TOP, B0, B1 ),
	normalize_wti_2( VarType, HLDS, B1, TOP, SEL0, SEL).

:- pred normalize_wti_2( type, module_info, branch_map, 
				selector, selector, selector).
:- mode normalize_wti_2( in, in, in, in, in, out) is det.

normalize_wti_2( VarType, HLDS, B0, Acc0, SEL0, SEL ):-
	(
		top( SEL0 )
	->
		SEL = Acc0
	;
		select_first_part( SEL0, US, SELR ),
		US = us(CONS, INDEX), 
		type_util__classify_type( VarType, HLDS, Class ),
		(
			Class = user_type
		->
			type_util__get_cons_id_arg_types(HLDS, VarType, CONS,
							ArgTypes ),
			(
				list__index1(ArgTypes, INDEX, CType )
			->
				( 
					branch_map_search( B0, CType, BSel )
				->
					normalize_wti_2( CType, HLDS,
							B0, BSel, SELR, SEL )
				;
					unit_termshift( Acc0, US, Acc1 ),
					branch_map_insert( CType, Acc1, B0, B1 ),
					normalize_wti_2( CType, HLDS, 
							B1, Acc1, SELR, SEL )
				)
			;

				get_type_defn(HLDS,VarType,TypeDefn),
				get_type_id(VarType,TypeID),
				hlds_data__get_type_defn_status(TypeDefn,
					TypeImportStatus),
				hlds_data__get_type_defn_body(TypeDefn,
					TypeBody), 

				hlds_type_body_to_minimal_string(TypeBody,
					BodyString),
		hlds_pred__import_status_to_minimal_string(TypeImportStatus,
					StatusString),
				type_util__type_id_name(HLDS,TypeID,TypeName),
				type_util__type_id_module(HLDS,TypeID,
						ModuleName),
				prog_out__sym_name_to_string(ModuleName,
						"__", SModuleName),	
				hlds_out__cons_id_to_string(CONS,SCONS),
				string__int_to_string(INDEX,SINDEX),

				string__append_list([
		"\n(pa_selector) normalize_wti_2: index not found.\n",
		"(pa)              type is ", SModuleName, "::",TypeName, 
				" -> ", SCONS, " -- ", SINDEX, "\n",
		"(pa)              (", BodyString, " and ", 
					StatusString, ").\n"], Msg),
	
			%	error("(pa) pa_alias_as: index not found.")
				error(Msg)
			)
		;
			% if it's not a user type, SELR will be empty
			% anyhow, and normalization stops.
			% Resulting selector = accumulator.sel0
			% selector_add_us( Acc0, US, SEL)
			append(Acc0,SEL0,SEL)

		)
	).

:- pred get_type_id((type),type_id).
:- mode get_type_id(in,out) is det.

get_type_id( Type, TypeID ):- 
	(
		type_util__type_to_type_id(Type, TypeID0, _)
	->
		TypeID = TypeID0
	;
		error("(pa_selector) get_type_id: type is not a non-variable type.")
	).

:- pred get_type_defn(module_info,(type),hlds_type_defn).
:- mode get_type_defn(in,in,out) is det.

get_type_defn(HLDS,VarType,TypeDefn):-
	(
		type_to_type_id(VarType,TypeId,_TypeArgs),
		module_info_types(HLDS,Types),
		map__lookup(Types,TypeId,TypeDefn0)
	->
		TypeDefn = TypeDefn0
	;
		error("(pa_selector) get_type_defn: no type definition")
	).

:- pred hlds_type_body_to_minimal_string(hlds_type_body, string).
:- mode hlds_type_body_to_minimal_string(in,out) is det.

hlds_type_body_to_minimal_string(du_type(_,_,_,_), "du_type").
hlds_type_body_to_minimal_string(uu_type(_), "uu_type").
hlds_type_body_to_minimal_string(eqv_type(_), "eqv_type").
hlds_type_body_to_minimal_string(abstract_type, "abstract_type").



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

