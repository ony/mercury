%-----------------------------------------------------------------------------%
% Copyright (C) 2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% This module contains the printing and parsing routines for the public types
% used for the possible-alias and structure reuse analysis. 
% author: nancy

:- module parse_tree__prog_io_pasr.

:- interface. 

:- import_module parse_tree__prog_data.

:- import_module io, term.

%-----------------------------------------------------------------------------%
% Printing routines. 
%-----------------------------------------------------------------------------%
% 
% 1. selector. 
:- pred print_selector(tvarset::in, selector::in, io__state::di, 
		io__state::uo) is det.

% 2. datastruct.
:- pred print_datastruct(prog_varset::in, tvarset::in, datastruct::in, 
		io__state::di, io__state::uo) is det.

% 3. alias.
:- pred print_alias(prog_varset::in, tvarset::in, string::in, string::in, 
		alias::in, io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
% Transform to string routines. 

% 1. selectors
	% The same as print_selector, yet returns a string instead of printing
	% the result to stdout. 
:- pred selector_to_string(tvarset::in, selector::in, string::out) is det.

	% User declared selectors are constrained to type selectors only. Hence
	% this procedure will give an error when a normal selector is
	% encountered. 
:- pred to_user_declared_selector(tvarset::in, selector::in, 
		string::out) is det. 

% 2. datastructs. 
:- pred to_user_declared_datastruct(prog_varset::in, tvarset::in, 
		datastruct::in, string::out) is det. 

%-----------------------------------------------------------------------------%
% Parsing routines. 
%-----------------------------------------------------------------------------%

% 1. selector. 
:- pred parse_selector(term(T)::in, selector::out) is det.
% 2. datastruct. 
:- pred parse_datastruct(term(T)::in, datastruct::out) is det.
% 3. alias.
:- pred parse_alias(term(T)::in , alias::out) is det.


%-----------------------------------------------------------------------------%

:- implementation. 

:- import_module hlds. 
:- import_module hlds__hlds_data.
:- import_module parse_tree__mercury_to_mercury.
:- import_module parse_tree__prog_io.

:- import_module string, list, require, bool, varset, std_util. 

%-----------------------------------------------------------------------------%
print_selector(TVarSet, Selector, !IO) :-
	selector_to_string(TVarSet, Selector, String), 
	io__write_string(String, !IO). 

print_datastruct(ProgVarSet, TypeVarSet, DataStruct, !IO) :- 
	varset__lookup_name(ProgVarSet, DataStruct^sc_var, VarName),
	io__write_strings(["cel(", VarName, ", "], !IO), 
	print_selector(TypeVarSet, DataStruct^sc_selector, !IO),
	io__write_string(")", !IO).

print_alias(ProgVarSet, TypeVarSet, FrontString, EndString, Alias0, !IO) :- 
	Alias0 = D1 - D2,
	io__write_string(FrontString, !IO),
	io__write_string("pair(", !IO),
	print_datastruct(ProgVarSet, TypeVarSet, D1, !IO),
	io__write_string(" , ", !IO),
	print_datastruct(ProgVarSet, TypeVarSet, D2, !IO),
	io__write_string(") ", !IO),
	io__write_string(EndString, !IO).
%-----------------------------------------------------------------------------%
to_user_declared_selector(TVarSet, Selector, String):- 
	(
		Selector = []
	-> 
		String = "[]"
	; 
		list__map(us_to_user_declared(TVarSet), 
			Selector, SelectorStrings), 
		string__append_list(["[", 
			string__join_list(",", SelectorStrings), 
			"]"], String)
	). 

selector_to_string(TVarSet, Selector, String):- 
	(
		Selector = []
	-> 
		String = "[]"
	; 
		list__map(us_to_string(TVarSet), 
			Selector, SelectorStrings), 
		string__append_list(["[", 
			string__join_list(",", SelectorStrings), 
			"]"], String)
	). 

:- pred us_to_string(tvarset::in, unit_sel::in, string::out) is det.
us_to_string(_, ns(ConsId, Index), StringSelector):- 
	hlds_data__cons_id_arity(ConsId, Arity), 
	string__append_list(["sel(",
		mercury_cons_id_to_string(ConsId, needs_brackets),
		",", 
		int_to_string(Arity), 
		",",
		int_to_string(Index), 
		")"], StringSelector).

us_to_string(TVarSet, ts(TypeSel), StringSelector):- 
	string__append_list(["typesel(", 
		mercury_term_to_string(TypeSel, TVarSet, bool__no),
		")"], StringSelector).

:- pred us_to_user_declared(tvarset::in, unit_sel::in, string::out) is det.
us_to_user_declared(_, ns(_, _), _):- 
	Msg = "(pa_selector) us_to_user_declared, expected type-selectors.",
	require__error(Msg). 
us_to_user_declared(TVarSet, ts(Type), String) :- 
	String = mercury_type_to_string(TVarSet, Type). 

%-----------------------------------------------------------------------------%
% 2. datastruct. 
to_user_declared_datastruct(ProgVarSet, TypeVarSet, Data, String):- 
	Data = selected_cel(ProgVar, Selector), 
	varset__lookup_name(ProgVarSet, ProgVar, ProgName), 
	to_user_declared_selector(TypeVarSet, Selector,
			SelectorString), 
	string__append_list(["cel(", ProgName, ", ", SelectorString, ")"], 
		String). 


%-----------------------------------------------------------------------------%
% Parsing routines. 
%-----------------------------------------------------------------------------%
% 
% 1. selector.
parse_selector(Term, Sel):- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "[|]",
			Args = [ First , Rest ]
		->
			parse_unit_selector(First, US),
			parse_selector(Rest, SelRest),
			Sel = [ US | SelRest ]
		;
			Sel = []
		)
	;
		error("(prog_io_pasr) parse_selector: term not a functor")
	).

:- pred parse_unit_selector(term(T)::in, unit_sel::out) is det.

parse_unit_selector(Term, US):- 
   (
      Term = term__functor(term__atom(Cons), Args, _)
   ->
      (
         Cons = "sel",
         Args = [ ConsTerm, ArityTerm, PosTerm ]
      ->
         (
            prog_io__sym_name_and_args(ConsTerm, ConsID_SN, ConsID_Args),
            ConsID_Args = [],
	    ArityTerm = term__functor(term__integer(Arity), _, _),
            PosTerm = term__functor(term__integer(Pos), _, _)
         ->
	    ConsID = cons(ConsID_SN, Arity),
	    US = ns(ConsID, Pos)
	 ;
	    ConsTerm = term__functor(term__integer(X), _, _)
	 ->
	    ConsID = int_const(X), 
	    US = ns(ConsID, 0)
	 ;
	    ConsTerm = term__functor(term__float(X), _, _)
	 ->
	    ConsID = float_const(X),
	    US = ns(ConsID, 0)
	 ;
	    ConsTerm = term__functor(term__string(S), _, _)
	 ->
	    ConsID = string_const(S),
	    US = ns(ConsID, 0)
	 ;
	    error("(prog_io_pasr) parse_unit_selector: unknown cons_id in unit selector")
	 )
      ; 
	 
         Cons = "typesel",
	 Args = [ TypeSelectorTerm ]
      ->
 	 term__coerce(TypeSelectorTerm, TypeSelector), 
	 US = ts(TypeSelector)
      ;
	 error("(prog_io_pasr) parse_unit_selector: top constructor should be sel/3 or typesel/1.")
      )
   ;
      error("(prog_io_pasr) parse_unit_selector: term not a functor")
   ).

%-----------------------------------------------------------------------------%
% 2. datastruct. 
parse_datastruct(TERM, Data) :- 
   (
      TERM = term__functor(term__atom(CONS), Args, _)
   ->
      (
         CONS = "cel"
      ->
         (
            Args = [ VarTerm, SelectorTerm ]
         ->
           (
              VarTerm = term__variable(VAR)
	   ->
	      term__coerce_var(VAR, PROGVAR),
	      parse_selector(SelectorTerm, SELECTOR),
	      Data = selected_cel(PROGVAR, SELECTOR)
	   ;
	      error("(prog_io_pasr) parse_datastruct: wrong term. variable, should be functor")
	   )
	 ;
	   list__length(Args, L),
	   string__int_to_string(L, LS),
	   string__append_list(["(prog_io_pasr) parse_datastruct: wrong number of arguments. cel/",LS,
	   			"should be cel/2"],Msg),
	   error(Msg)
	 )
      ;
         string__append_list(["(pa_datastruct) parse_term: wrong constructor. `",CONS,
	 			"' should be `cel'"],Msg),
	   error(Msg)
      )
   ;
      error("(prog_io_pasr) parse_datastruct: term not a functor")
   ).

%-----------------------------------------------------------------------------%
% 3. alias
parse_alias(Term,  A) :- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "pair"
		->
			(
				Args = [ First, Second ]
			->
				parse_datastruct(First, D1),
				parse_datastruct(Second, D2),
				A = D1 - D2
			;
				list__length(Args, L),
				string__int_to_string(L,LS),
				string__append_list(
					[ "(prog_io_pasr) parse_alias: ", 
					"wrong number of arguments. `-'/",
					LS," should be `-'/2"],Msg),
				error(Msg)
			)
		;
			term__det_term_to_type(Term, Type),
			varset__init(V),
			StringTerm = mercury_type_to_string(V, Type),
			string__append_list([ 
					"(prog_io_pasr) parse_alias: ",
					"wrong constructor. `",
					StringTerm,
					"' should be `pair'"],Msg),
			error(Msg)
		)
	;
		error("(prog_io_pasr) parse_alias: term is not a functor")
	).

