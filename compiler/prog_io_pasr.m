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

:- import_module io, term, std_util, list, varset, map.


% XXX prog_io_pasr shows to be a bad name, if it also contains procedures to
% transform the aliases types, like the renaming below. 
%-----------------------------------------------------------------------------%
% Renaming
%-----------------------------------------------------------------------------%
:- pred rename_selector(substitution(tvar_type)::in,
		selector::in, selector::out) is det.
:- pred rename_datastruct(map(prog_var, prog_var)::in, 
		maybe(substitution(tvar_type))::in,
		datastruct::in, datastruct::out) is det.
:- pred rename_alias(map(prog_var, prog_var)::in, 
		maybe(substitution(tvar_type))::in,
		alias::in, alias::out) is det.
:- pred rename_aliases(map(prog_var, prog_var)::in, 
		maybe(substitution(tvar_type))::in,
		aliases::in, aliases::out) is det.
:- pred rename_aliases_domain(map(prog_var, prog_var)::in, 
		maybe(substitution(tvar_type))::in,
		aliases_domain::in, aliases_domain::out) is det.
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

% 4. aliases.
	% print_aliases(ProgVarSet, TypeVarSet, MaybeThreshold, 
	%	StartString, Separator, EndString, Aliases, !IO).
	% Print the set of aliases using StartString to precede the set of
	% aliases, using EndString to end the set of aliases, using Separator
	% to separate each of the aliases occuring in the list. If a threshold,
	% say N, is given, then only the first N aliases are printed. 
:- pred print_aliases(prog_varset::in, tvarset::in, maybe(int)::in, 
		string::in, string::in, string::in, aliases::in, 
		io__state::di, io__state::uo) is det.

% 5. aliases_domain.
	% Print the aliases as either "top", "bottom", or as a list of 
	% alias-pairs. If a threshold N is given, then only print the first N
	% aliases of the list of aliases.
:- pred print_aliases_domain(prog_varset::in, tvarset::in, 
		maybe(int)::in, aliases_domain::in,
		io__state::di, io__state::uo) is det.

% 6. maybe(aliases_domain).
	% Print the aliases as a mercury-comment, used in the hlds-dump. 
	% The msg's in top-aliases are fully printed. 
:- pred dump_maybe_aliases_domain(prog_varset::in, tvarset::in, 
		maybe(aliases_domain)::in, 
		io__state::di, io__state::uo) is det.

% 7. reuse_tuple.
:- pred print_reuse_tuple(prog_varset::in, tvarset::in, reuse_tuple::in, 
		io__state::di, io__state::uo) is det.

	% The sym_name is the name of the reuse-predicate for which the
	% reuse-conditions are valid. 
:- pred print_maybe_reuse_tuples(prog_varset::in, tvarset::in, 
		maybe_reuse_tuples::in, maybe(sym_name)::in, 
		io__state::di, io__state::uo) is det.


	% Print the aliases in a form suitable for the transitive-optimisation
	% files. The msg's in top-aliases are discarded: a top alias set is
	% simply printed as "top". 
:- pred print_interface_maybe_aliases_domain(prog_varset::in, tvarset::in, 
		maybe(aliases_domain)::in, 
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
% Parsing routines. 
%-----------------------------------------------------------------------------%

% 1. selector. 
:- pred parse_selector(term(T)::in, selector::out) is det.
% 2. datastruct. 
:- pred parse_datastruct(term(T)::in, datastruct::out) is det.
% 3. alias.
:- pred parse_alias(term(T)::in , alias::out) is det.
% 4. aliases
:- pred parse_aliases(term(T)::in, aliases::out) is det.
% 5. aliases_domain
:- pred parse_aliases_domain(term(T)::in, aliases_domain::out) is det.
:- pred parse_aliases_domain_from_list(list(term(T))::in,
		aliases_domain::out) is det.
	% Parse the used declared aliases (pragma aliasing). 
:- pred parse_user_declared_aliasing(term::in, varset::in, 
		aliasing::out) is semidet.
% 6. reuse_tuple
:- pred parse_reuse_tuple(term(T)::in, reuse_tuple::out) is det.
% 7. maybe_reuse_tuple
:- pred parse_maybe_reuse_tuples(term(T)::in, maybe_reuse_tuples::out, 
	maybe(sym_name)::out) is semidet.

:- pred format_context(term__context::in, string::out) is det.
%-----------------------------------------------------------------------------%

:- implementation. 

:- import_module hlds. 
:- import_module hlds__hlds_data.
:- import_module parse_tree__mercury_to_mercury.
:- import_module parse_tree__prog_io.
:- import_module parse_tree__prog_out.
:- import_module parse_tree__prog_io_util.

:- import_module string, require, bool, varset, std_util, int, set. 

%-----------------------------------------------------------------------------%
:- pred rename_unit_selector(substitution(tvar_type)::in, 
		unit_sel::in, unit_sel::out) is det.
rename_unit_selector(Subst, US0, US) :- 
	(
		US0 = ns(_,_), 
		US = US0
	; 
		US0 = ts(Type0), 
		term__apply_substitution(Type0, Subst, Type), 
		US = ts(Type)
	).
rename_selector(TypeSubst, Sel0, Sel) :- 
	list__map(rename_unit_selector(TypeSubst), Sel0, Sel).

rename_datastruct(ProgMap, MaybeTypeSubst, Data0, Data) :- 
	Data0 = selected_cel(Var0, Sel0), 
	map__lookup(ProgMap, Var0, Var), 
	(
		MaybeTypeSubst = yes(TypeSubst), 
		rename_selector(TypeSubst, Sel0, Sel)
	;
		MaybeTypeSubst = no, 
		Sel = Sel0
	),
	Data = selected_cel(Var, Sel). 
rename_alias(ProgMap, MaybeTypeSubst, A0 - B0, A - B) :- 
	rename_datastruct(ProgMap, MaybeTypeSubst, A0, A), 
	rename_datastruct(ProgMap, MaybeTypeSubst, B0, B).

rename_aliases(ProgMap, MaybeTypeSubst, Aliases0, Aliases) :- 
	list__map(rename_alias(ProgMap, MaybeTypeSubst), Aliases0, Aliases).

rename_aliases_domain(_, _, top(M), top(M)).
rename_aliases_domain(_, _, bottom, bottom).
rename_aliases_domain(ProgMap, MaybeTypeSubst, real(Aliases0), real(Aliases)):- 
	rename_aliases(ProgMap, MaybeTypeSubst, Aliases0, Aliases).
%-----------------------------------------------------------------------------%

:- pred selector_to_string(tvarset::in, selector::in, string::out) is det.
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

:- pred print_alias(prog_varset::in, tvarset::in, alias::in, 
		io__state::di, io__state::uo) is det.
print_alias(ProgVarSet, TypeVarSet, Alias0, !IO) :- 
	Alias0 = D1 - D2,
	io__write_string("pair(", !IO),
	print_datastruct(ProgVarSet, TypeVarSet, D1, !IO),
	io__write_string(", ", !IO),
	print_datastruct(ProgVarSet, TypeVarSet, D2, !IO),
	io__write_string(")", !IO).

print_aliases(ProgVarSet, TypeVarSet, yes(Limit), Start, Sep, End, 
		Aliases, !IO) :- 
	list__take_upto(Limit, Aliases, Aliases1), 
	io__write_string(Start, !IO), 
	print_aliases_2(ProgVarSet, TypeVarSet, Sep, 
			Aliases1, !IO), 
	io__write_string(Sep, !IO), 
	io__write_string("...", !IO), 
	io__write_string(End, !IO). 

print_aliases(ProgVarSet, TypeVarSet, no, 
		Start, Sep, End, Aliases, !IO) :- 
	io__write_string(Start, !IO), 
	print_aliases_2(ProgVarSet, TypeVarSet, Sep, 
			Aliases, !IO), 
	io__write_string(End, !IO).

:- pred print_aliases_2(prog_varset::in, tvarset::in, string::in, 
		aliases::in, io__state::di, io__state::uo) is det.

print_aliases_2(ProgVarSet, TypeVarSet, Sep, Aliases, !IO) :- 
	io__write_list(Aliases, Sep, 
		print_alias(ProgVarSet, TypeVarSet), !IO).

dump_maybe_aliases_domain(_ProgVarSet, _TypeVarSet, no, !IO) :- 
	io__write_string("not available.\n", !IO).
dump_maybe_aliases_domain(ProgVarSet, TypeVarSet, yes(AliasesDomain), !IO) :- 
	(
		AliasesDomain = bottom,
		io__write_string("aliases are bottom.\n", !IO)
	; 
		AliasesDomain = top(Msgs),
		TopString = string__join_list("\n%\t", Msgs),
		io__write_string("aliases are top: \n%\t", !IO),
		io__write_string(TopString, !IO),
		io__nl(!IO)
	;
		AliasesDomain = real(Aliases),
		print_aliases(ProgVarSet, TypeVarSet, no, 
			"\n% ", "\n% ", "\n", Aliases, !IO)
	).

print_interface_maybe_aliases_domain(_ProgVarSet, _TVarSet, no, !IO) :- 
	io__write_string("not_available", !IO). 
print_interface_maybe_aliases_domain(ProgVarSet, TVarSet, yes(Aliases), !IO) :-
	io__write_string("yes(", !IO), 
	print_aliases_domain(ProgVarSet, TVarSet, no, Aliases, !IO), 
	io__write_string(")", !IO). 

print_aliases_domain(ProgVarSet, TVarSet, MaybeThreshold, Aliases, !IO) :- 
	(
		Aliases = top(_),
		io__write_string("top", !IO)
	; 
		Aliases = bottom,
		io__write_string("bottom", !IO)
	; 
		Aliases = real(AliasList), 
		print_aliases(ProgVarSet, TVarSet, MaybeThreshold, "[", ", ", 
			"]", AliasList, !IO)
	).

print_reuse_tuple(_ProgVarSet, _TVarSet, unconditional, !IO) :- 
	io__write_string("always", !IO).
print_reuse_tuple(ProgVarSet, TVarSet, conditional(Nodes, LUiH, LAiH), !IO) :-
	set__to_sorted_list(Nodes, NodesList),
	set__to_sorted_list(LUiH, ListLUiH),
	ListLUiHVars = list__map( 
		(func(D) = V :- V = D ^ sc_var), ListLUiH), 

	io__write_string("condition(", !IO),
		% write out the list of headvar-nodes involved
	io__write_string("[", !IO),
	io__write_list(NodesList, ",", 
			print_datastruct(ProgVarSet, TVarSet), !IO), 
	io__write_string("], ", !IO),	

		% write out LUiH, list of prog_vars
	io__write_string("[", !IO),
	mercury_output_vars(ListLUiHVars, ProgVarSet, bool__no, !IO), 
	io__write_string("], ", !IO),

		% write out LAiH, the aliases at the reuse-point
	print_aliases_domain(ProgVarSet, TVarSet, no, LAiH, !IO),
	io__write_string(")", !IO).

print_maybe_reuse_tuples(_, _, no, _, !IO) :- 
	io__write_string("no", !IO).
print_maybe_reuse_tuples(ProgVarSet, TVarSet, yes(Tuples), MaybeName, !IO) :- 
	io__write_string("yes([", !IO), 
	io__write_list(Tuples, ",", 
		print_reuse_tuple(ProgVarSet, TVarSet), !IO), 
	io__write_string("]", !IO), 
	(
		MaybeName = yes(Name)
	-> 
		io__write_string(",", !IO), 
		prog_out__write_quoted_sym_name(Name, !IO)
	;
		true
	),
	io__write_string(")", !IO). 

	
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

%-----------------------------------------------------------------------------%
% 4. aliases
parse_aliases(Term, Aliases) :-
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
		        Cons = "[|]",
                        Args = [ AliasTerm, Rest]
                ->
			parse_alias(AliasTerm, Alias),
			parse_aliases(Rest, RestAliases), 
                        Aliases = [ Alias | RestAliases ]
                ;
			Cons = "[]"
		->
			Aliases = []
		;
			string__append("(prog_io_pasr) parse_aliases: could not parse aliases, top cons: ", Cons, Msg),
			error(Msg)
		)
        ;
                error("(prog_io_pasr) parse_aliases: term is not a functor")
	).

%-----------------------------------------------------------------------------%
% 4. aliases_domain
parse_aliases_domain(Term, AS) :- 
	(
		Term = term__functor(term__atom(Cons), _Terms, Context)
	->
		(
			Cons = "[|]"
		->
			parse_aliases(Term, Aliases),
			AS = real(Aliases)
		;
			Cons = "bottom"
		->
			AS = bottom

		; 
			Cons = "top"
		->
			format_context(Context, ContextString), 
			string__append_list(["imported top (", 
				ContextString, ")"], 
					Msg),
			AS = top([Msg])
		;
			string__append(
		"(prog_io_pasr) parse_aliases_domain: could not parse aliases, top cons: ", Cons, Msg),
			error(Msg)
		)
	;
		error("(prog_io_pasr) parse_aliases_domain: term not a functor")
	).

format_context(Context, String):- 
	term__context_line(Context, ContextLine), 
	term__context_file(Context, ContextFile), 
	string__int_to_string(ContextLine, ContextLineS), 
	string__append_list([ContextFile, ":", ContextLineS], 
			String).

parse_aliases_domain_from_list(ListTerm, AliasesDomain):- 
	(
		% ListTerm must have only one item
		ListTerm = [ Term ]
	->
		parse_aliases_domain(Term, AliasesDomain)
	;
		list__length(ListTerm, L),
		string__int_to_string(L, LS), 
		string__append_list([
			"(prog_io_pasr) ", 
			"parse_aliases_domain_from_list: ", 
			"wrong number of arguments. yes/", LS,
			" should be yes/1"], Msg),
		error(Msg)
	).

:- pred parse_user_declared_datastruct(term::in, datastruct::out) is det. 
parse_user_declared_datastruct(Term, Data):- 
	(
		Term = term__functor(term__atom("cel"),
			[VarTerm, TypesTerm], Context)
	->
		(
			VarTerm = term__variable(GenericVar),
			term__coerce_var(GenericVar, ProgVar) 
		-> 
			(
				split_terms(TypesTerm, ListTypesTerms)
			-> 
				list__map(term__coerce, ListTypesTerms, Types),
				Data = selected_cel(ProgVar, 
					typeselector_init(Types))
			;
				format_context(Context, ContextString), 
				string__append_list([
					"(prog_io_pasr) ",
					"parse_user_declared_datastruct: ", 
					"error in declared selector (", 
						ContextString, ")"], Msg), 
				error(Msg)
				
			)
		;
			format_context(Context, ContextString), 
			string__append_list([
				"(prog_io_pasr) ",
				"parse_user_declared_datastruct: ", 
				"error in declared alias (", 
				ContextString, ")"], Msg), 
			error(Msg)
		)
	;
		string__append_list(["(prog_io_pasr) ", 
			"parse_user_datastruct: ",
			"wrong datastructure description ",
			"-- should be cel/2"], Msg),
		error(Msg)
	).

:- pred parse_user_declared_alias(term::in, alias::out) is det.
parse_user_declared_alias(Term, Alias):- 
	(
		Term = term__functor(term__atom("-"), [Left, Right], _)
	->
		% Left and Right have shape "cel(ProgVar, Types)"
		parse_user_declared_datastruct(Left, LeftData), 
		parse_user_declared_datastruct(Right, RightData), 
		Alias = LeftData - RightData
	;
		string__append_list(["(prog_io_pasr) ", 
			"parse_user_declared_alias: ", 
			"wrong functor."], Msg), 
		error(Msg)
	).

:- pred parse_user_declared_aliases(term::in, aliases_domain::out) is det.
parse_user_declared_aliases(ListTerm, AliasDomain):- 
	(
		split_terms(ListTerm, AllTerms)
	-> 
		list__map(parse_user_declared_alias, 
				AllTerms, Aliases),
		AliasDomain = real(Aliases)
	;
		string__append_list(["(prog_io_pasr) ", 
			"parse_user_declared_aliases: ", 
			"term not a functor."], Msg), 
		error(Msg)
	).

:- pred split_terms(term::in, list(term)::out) is semidet.
split_terms(ListTerm, Terms):- 
	ListTerm = term__functor(term__atom(Cons), Args, _), 
	(
		Cons = "[|]"
	->
		Args = [FirstTerm, RestTerm],
		split_terms(RestTerm, RestList), 
		Terms = [FirstTerm | RestList]
	;
		Cons = "[]"
	->
		Terms = []
	; 
		fail
	). 

	% bottom
parse_user_declared_aliasing(term__functor(term__atom("no_aliasing"), [], _),
		_VarSet, Aliasing):-
	Aliasing = aliasing(no, varset__init, bottom). 
	% top
parse_user_declared_aliasing(term__functor(term__atom("unknown_aliasing"), 
				[], Context), _VarSet, Aliasing):-
	format_context(Context, ContextString), 
	string__append_list(["user declared top (", ContextString, ")"], Msg),
	TopAlias = top([Msg]),
	Aliasing = aliasing(no, varset__init, TopAlias). 
parse_user_declared_aliasing(term__functor(term__atom("alias"), 
		[TypesTerm,AliasTerm], _), VarSet, Aliasing):-
	(
		TypesTerm = term__functor(term__atom("yes"), 
					ListTypesTerms, _), 
		term__vars_list(ListTypesTerms, TypeVars), 
		set__list_to_set(TypeVars, SetTypeVars), 
		varset__select(VarSet, SetTypeVars, TypeVarSet0),
		varset__coerce(TypeVarSet0, TypeVarSet),
		
		list__map(term__coerce, ListTypesTerms, Types), 
		MaybeTypes = yes(Types)
	;
		TypesTerm = term__functor(term__atom("no"),[],_), 
		MaybeTypes = no,
		varset__init(TypeVarSet) 
	), 
	parse_user_declared_aliases(AliasTerm, AliasAs), 
	Aliasing = aliasing(MaybeTypes, TypeVarSet, AliasAs). 

	% Note that in the interfaces, unconditional reuse tuples are simply
	% not printed, therefore, there is no need to parse such tuples. 
parse_reuse_tuple(Term, ReuseTuple) :- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "condition"	
		->
			(
				Args = [NodesTerm, LUiHTerm, LAiHTerm]
			->
				nodes_parse(NodesTerm, NodesList),
				set__list_to_set(NodesList, Nodes), 
				vars_parse(LUiHTerm, LUiH),
				LUiHData = set__map(
					(func(V) = selected_cel(V,[])), 
					LUiH), 
				parse_aliases_domain(LAiHTerm, 	
						LAiH),
				ReuseTuple = conditional(Nodes, LUiHData, LAiH)
			;
				list__length(Args, L),
				string__int_to_string(L, LS), 
				string__append_list( 
					[ "(prog_io_pasr) condition_parse: ",
					"wrong number of arguments. ",
					"condition/",LS, " should be ",
					"condition/3"], Msg),
				error(Msg)
			)
		;
			term__det_term_to_type(Term, Type),
			varset__init(V), 
			StringTerm = mercury_type_to_string(V, Type),
			string__append_list( 
				["(prog_io_pasr) condition_parse: ",
				"wrong constructur. `", 
				StringTerm, 
				"' should be `condition'"], Msg),
			error(Msg)
		)
	;
		error("(prog_io_pasr) condition_parse: term is not a functor")
	).

:- pred vars_parse(term(T)::in, set(prog_var)::out) is det.

vars_parse(Term, Vars) :- 
	vars_parse_list(Term, VarList) , 
	set__list_to_set(VarList, Vars).

:- pred vars_parse_list(term(T)::in, list(prog_var)::out) is det.

vars_parse_list(Term, Vars) :- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "[|]",
			Args = [First, Rest]
		->
			( 
				First = term__variable(V)
			->
				V1 = V
			;
				error("(prog_io_pasr) vars_parse_list: list should contain variables.")
			),	
			term__coerce_var(V1, ProgVar),
			vars_parse_list(Rest, V2),
			Vars = [ProgVar | V2]
		;
			Cons = "[]"
		->
			Vars = []
		;
			string__append("(prog_io_pasr) vars_parse_list: could not parse nodes, top cons: ", Cons, Msg),
			error(Msg)
		)
	;
		error("(prog_io_pasr) vars_parse_list: term not a functor")
	).

:- pred nodes_parse(term(T)::in, list(datastruct)::out) is det.

nodes_parse(Term, Datastructs) :- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "[|]",
			Args = [First, Rest]
		->
			parse_datastruct(First, D1),
			nodes_parse(Rest, D2),
			Datastructs = [D1 | D2]
		;
			Cons = "[]"
		->
			Datastructs = []
		;
			string__append("(prog_io_pasr) nodes_parse: could not parse nodes, top cons: ", Cons, Msg),
			error(Msg)
		)
	;
		error("(prog_io_pasr) nodes_parse: term not a functor")
	).

:- pred parse_reuse_tuples(term(T)::in, list(reuse_tuple)::out) is det.
parse_reuse_tuples(Term, Tuples) :- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "[|]",
			Args = [First, Rest]
		->
			parse_reuse_tuple(First, Cond1),
			parse_reuse_tuples(Rest, Cond2),
			Tuples = [Cond1 | Cond2]
		;
			Cons = "[]"
		->
			Tuples = []
		;
			string__append_list([
				"(prog_io_pasr) parse_reuse_tuples: ",
				"could not parse conditions, top cons: ", 
				Cons], Msg),
			error(Msg)
		)
	;
		error("(prog_io_pasr) parse_reuse_tuples: term not a functor")
	).


parse_maybe_reuse_tuples(Term, MaybeReuseTuples, MaybeReuseName) :- 
	(
		Term = term__functor(term__atom("no"), _, _),
		MaybeReuseName = no,
		MaybeReuseTuples = no
	;
		Term = term__functor(term__atom("yes"),
					ReadTuplesAndName, _),
		(
			ReadTuplesAndName = [ReadTuples, NameTerm]
		->
			parse_reuse_tuples(ReadTuples, Tuples),
			MaybeReuseTuples = yes(Tuples),
			parse_qualified_term(NameTerm, 
				NameTerm, "pragma reuse",
				Result),
			(
				Result = ok(ReuseName, []) 
			->
				MaybeReuseName = yes(ReuseName)
			;
				string__append_list([
					"(prog_io_pasr) ", 
					"parse_maybe_reuse_tuples"], Msg), 
				error(Msg)
			)
		; 
			list__length(ReadTuplesAndName, L), 
			string__int_to_string(L, LS), 
			string__append_list([
				"(sr_data) conditions_list_parse: ",
				"wrong number of arguments. yes/", LS,
				" should be yes/2"], Msg),
			error(Msg)
		)
	).

:- func typeselector_init(list(type)) = selector. 
typeselector_init(Types) = Selector :- 
	list__map(
		pred(T::in, US::out) is det :- 
			US = ts(T),
		Types,
		Selector). 	

