%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_alias: manipulation of the type "alias", essential component
% 	of the abstract datatype alias_as, used during possible alias
% 	analysis.
% main author: nancy

:- module pa_alias.

:- interface.

%-------------------------------------------------------------------%
%-- import_module 

% library module
:- import_module set, list, std_util, map.
:- import_module io, string, term.

% compiler module
:- import_module prog_data.
:- import_module hlds_pred, hlds_goal, hlds_module.
:- import_module sr_live.
:- import_module pa_datastruct.

%-------------------------------------------------------------------%
%-- exported types

% :- type alias.
:- type alias == pair(datastruct).

%-------------------------------------------------------------------%
%-- exported predicates

	% Extract the vars from the alias.
:- pred alias_vars( alias, pair(prog_var)).
:- mode alias_vars( in, out ) is det.

	% Check whether the alias concerns variables which belong to 
	% the given set. 
:- pred contains_vars( list(prog_var), alias).
:- mode contains_vars( in, in) is semidet.

:- pred contains_one_of_vars_in_list( list(prog_var), alias).
:- mode contains_one_of_vars_in_list( in, in) is semidet.

/*  was before:
:- pred project_alias( list(prog_var), alias, 
			list(alias), list(alias)).
:- mode project_alias( in, in, in, out) is det.
*/

	% aliased_to( AL, D1, D2) such that AL = D1 - D2
:- pred aliased_to( module_info, proc_info, alias, datastruct, datastruct ).
:- mode aliased_to( in, in, in, in, out) is semidet.

	% Rename the variables of the alias using the given mapping. 
:- pred rename( map(prog_var, prog_var), alias, alias).
:- mode rename( in, in, out) is det.
/*  was before: 
:- pred rename_alias( map(prog_var, prog_var), alias, 
			list(alias), list(alias)).
:- mode rename_alias( in, in, in, out) is det.
*/

:- pred rename_types( term__substitution(tvar_type)::in, 
			alias::in, alias::out) is det.

	% Check whether a given alias is a member of the given list. 
:- pred occurs_in( alias, list(alias)).
:- mode occurs_in( in, in ) is semidet.
/*  was before alias_occurs_in( list(alias), alias). */

	% Check whether two aliases are equal. 
:- pred equal( alias, alias ).
:- mode equal( in, in ) is semidet.
/* was before 
:- pred alias_equal( alias, alias ).
:- mode alias_equal( in, in ) is semidet.
*/

	% Check whether a given alias is already covered (subsumed) by
	% the given list of aliases.
	% proc_info, and module_info are needed for the normalization
	% which is done when checking subsumption. 
	% XXX at this moment normalization is not used for subsumption
:- pred subsumed_by_list( proc_info, module_info, alias, list(alias) ).
:- mode subsumed_by_list( in, in, in, in) is semidet.
/* was before:
:- pred alias_subsumed_by_list( proc_info, module_info, list(alias), alias ).
:- mode alias_subsumed_by_list( in, in, in, in) is semidet.
*/

	% less_or_equal( ProcInfo, HLDS, Alias1, Alias2)
	% Check whether the first alias is covered by the second one.	
:- pred less_or_equal( proc_info, module_info, alias, alias).
:- mode less_or_equal( in, in, in, in ) is semidet.
/* was before: 
:- pred alias_leq( proc_info, module_info, alias, alias).
:- mode alias_leq( in, in, in, in ) is semidet.
*/

:- pred add_subsuming(proc_info, module_info, 
				alias,list(alias),list(alias)).
:- mode add_subsuming(in, in, in,in, out) is det.
/* was before: alias_add_subsuming/5 */

:- pred least_upper_bound_lists(proc_info, module_info, 
				list(alias), list(alias), list(alias)).
:- mode least_upper_bound_lists(in, in, in, in, out) is det.

	% extend( ProcInfo, ModuelInfo, List1, List2, List)
	% Extend the first list with the second one, obtaining List.
	% List1 must be the old, initial set of aliases.
	% List2 is the list of new additional aliases.
	% Order is important, as the underlying implementation can then
	% provide some optimizations with regard to the plain normal
	% way of computing the result. 
:- pred extend( proc_info, module_info, list(alias), list(alias), 
		list(alias)).
:- mode extend( in, in, in, in, out) is det.

	% given a unification, extract the aliases it creates. 
	% assignmenents between primitive types do not lead to new
	% aliases. 
:- pred from_unification( proc_info, module_info, 
		hlds_goal__unification, hlds_goal__hlds_goal_info, 
		list(alias)).
:- mode from_unification( in, in, in, in, out) is det.
/* was before: 
:- pred alias_from_unification(proc_info, module_info, 
				hlds_goal__unification, alias_as).
:- mode alias_from_unification(in, in, in, out) is det.
*/

	% Normalize the given alias. Normalization can be done in
	% several ways. The goal of this operation is to simplify 
	% an alias as much as possible, and without losing too much
	% information. 
	% At this moment, simplification is done based on the type-info
	% of the variables involved: e.g. tail of a list, is reduced to 
	% list. 	
:- pred normalize_wti(proc_info, module_info, alias, alias).
:- mode normalize_wti(in, in, in, out) is det.

	% extend_prog_var_from_alias( Var, Alias, SetIn, SetOut )
	% Extend SetIn with additional program variables which are aliased
	% with Var.
:- pred extend_prog_var_from_alias( prog_var, alias, 
		set(prog_var), set(prog_var)).
:- mode extend_prog_var_from_alias( in, in, in, out) is det.

	% printing routines
:- pred print( proc_info, pred_info, string, string, 
			alias, io__state, io__state).
:- mode print( in, in, in, in, in, di, uo) is det.

	% parsing routines
:- pred parse_term( term(T), alias).
:- mode parse_term( in, out) is det.

:- pred live_from_in_use(set(prog_var), list(alias), live_set).
:- mode live_from_in_use(in, in, out) is det.

:- pred live_from_live0(module_info, proc_info, 
				live_set, list(alias), live_set).
:- mode live_from_live0(in, in, in, in, out) is det.

:- pred apply_widening( module_info::in, proc_info::in, alias::in, 
		alias::out) is det.
:- pred apply_widening_list( module_info::in, proc_info::in, list(alias)::in,
		list(alias)::out) is det.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
:- implementation.

% library module
:- import_module varset, require, int.

% compiler module
:- import_module hlds_data, mercury_to_mercury, type_util.
:- import_module pa_datastruct.
:- import_module pa_selector.

%-------------------------------------------------------------------%
%-- type definitions 

%:- type alias == pair(datastruct).

%-------------------------------------------------------------------%

extend_prog_var_from_alias( Var, Alias, Set0, Set):-
	(
		alias_vars( Alias, Var - OtherVar )
	->
		set__insert( Set0, OtherVar, Set)
	;
		alias_vars( Alias, OtherVar - Var )
	->
		set__insert( Set0, OtherVar, Set)
	;

		Set = Set0
	).
	


%-------------------------------------------------------------------%
% printing routines
%-------------------------------------------------------------------%

print( ProcInfo, PredInfo, FrontString, EndString, ALIAS ) -->
	{ ALIAS = D1 - D2 },
	io__write_string( FrontString ),
	io__write_string( "pair( " ),
	pa_datastruct__print( D1, ProcInfo, PredInfo ),
	io__write_string(" , "),
	pa_datastruct__print( D2, ProcInfo, PredInfo ),
	io__write_string(" ) "),
	io__write_string( EndString ).

%-------------------------------------------------------------------%
% parsing routines
%-------------------------------------------------------------------%

pa_alias__parse_term( TERM,  A) :- 
	(
		TERM = term__functor( term__atom(CONS), Args, _)
	->
		( 
			CONS = "pair"
		->
			(
				Args = [ First, Second ]
			->
				pa_datastruct__parse_term( First, D1 ),
				pa_datastruct__parse_term( Second, D2 ),
				A = D1 - D2
			;
				list__length(Args, L),
				string__int_to_string(L,LS),
				string__append_list(
					[ "(pa_alias) parse_term: ", 
					"wrong number of arguments. `-'/",
					LS," should be `-'/2"],Msg),
				error(Msg)
			)
		;
			term__det_term_to_type( TERM, TYPE),
			varset__init(V),
			mercury_type_to_string(V, TYPE, StringTerm),
			string__append_list([ 
					"(pa_alias) parse_term: ",
					"wrong constructor. `",
					StringTerm,
					"' should be `pair'"],Msg),
			error(Msg)
		)
	;
		error("(pa_alias) parse_term: term is not a functor")
	).


alias_vars( Data1 - Data2, Var1 - Var2 ):-
	pa_datastruct__get_var(Data1, Var1),
	pa_datastruct__get_var(Data2, Var2).

contains_vars( Vars, Alias) :- 
	Alias = Data1 - Data2,
	pa_datastruct__get_var(Data1, Var1),
	pa_datastruct__get_var(Data2, Var2),
	list__member(Var1, Vars),
	list__member(Var2, Vars).

contains_one_of_vars_in_list( Vars, Alias) :- 
	Alias = Data1 - Data2,
	pa_datastruct__get_var(Data1, Var1),
	pa_datastruct__get_var(Data2, Var2),
	( list__member(Var1, Vars);  list__member(Var2, Vars)).
	
aliased_to( ModuleInfo, ProcInfo, Alias, Data1, Data2 ) :-
	Alias = D1 - D2,
	(
		pa_datastruct__less_or_equal(ModuleInfo, ProcInfo, 
						Data1, D1, EXT)
	->
		pa_datastruct__termshift(D2, EXT, Data2)
	;
		pa_datastruct__less_or_equal(ModuleInfo, ProcInfo, 
						Data1, D2, EXT)
	->
		pa_datastruct__termshift(D1, EXT, Data2)
	;
		fail
	).
		

	% contains_one_of_vars( SET, ALIAS, DATA)
	% returns true if ALIAS = DATA1 - DATA, 
	%	where DATA1 \in SET
	% 	  and DATA  \not\in SET

:- pred contains_one_of_vars( set(prog_var), alias, datastruct).
:- mode contains_one_of_vars( in, in, out) is semidet.

contains_one_of_vars( Set, Alias, DATA) :- 
	Alias = Data1 - Data2,
	pa_datastruct__get_var(Data1, Var1),
	pa_datastruct__get_var(Data2, Var2),
	( 
		set__member(Var1, Set)
	->
		not(set__member(Var2, Set) ),
		DATA = Data2
	;
		set__member(Var2, Set) 
	->
		not(set__member(Var1, Set)),
		DATA = Data1
	;
		fail
	).


rename( MAP, Alias, RAlias) :-
	Alias = Data1 - Data2,
	pa_datastruct__rename( MAP, Data1, RData1),
	pa_datastruct__rename( MAP, Data2, RData2),
	RAlias = RData1 - RData2. 

rename_types( Subst, Alias0, Alias ):-
	Alias0 = Data10 - Data20, 
	pa_datastruct__rename_types( Subst, Data10, Data1), 
	pa_datastruct__rename_types( Subst, Data20, Data2), 
	Alias = Data1 - Data2.

occurs_in( A2, [A1 | R ] ):-
	(
		pa_alias__equal(A1,A2)
	-> 
		true
	;
		occurs_in( A2, R )
	). 

equal( A1, A2 ) :- 
	A1 = D1a - D1b,
	A2 = D2a - D2b,
	(
		pa_datastruct__equal(D1a,D2a),
		pa_datastruct__equal(D1b,D2b)
	;
		pa_datastruct__equal(D1a,D2b),
		pa_datastruct__equal(D1b,D2a)
	).

subsumed_by_list( ProcInfo, HLDS, A2, [A1 | R ] ) :- 
	(
		less_or_equal(ProcInfo, HLDS,A2,A1) 
	->
		true
	;
		subsumed_by_list( ProcInfo, HLDS, A2, R)
	).


less_or_equal( ProcInfo, HLDS, A1, A2 ) :-
	A1 = D1a - D1b,
	A2 = D2a - D2b,
	(
		% XXX TEST underscored extensions!
		pa_datastruct__less_or_equal(HLDS, ProcInfo, D1a,D2a, EXT1),
		pa_datastruct__less_or_equal(HLDS, ProcInfo, D1b,D2b, EXT1)
		% the extension should be the same wrt normalization
		% normalize(D1b.EXT1) == normalize(D1b.EXT2) 
		% where normalize(D1b.EXT2) == D2b as D2b is a normalized
		% datastructure. 
		% ==> normalize(D1b.EXT1) == D2b
		% datastruct_termshift(D1b, EXT1, D_temp), 
		% normalize_datastruct(ProcInfo,HLDS,D_temp,D2b)
		%  XXX 
		% verifying the leq-operation wrt normalize operation
		% is not really recommended as datastructs are not 
		% normalized during the analysis of a procedure, only
		% at the end. 
	;
		% XXX TEST underscored extensions!
		pa_datastruct__less_or_equal(HLDS, ProcInfo, D1a,D2b, EXT1),
		pa_datastruct__less_or_equal(HLDS, ProcInfo, D1b,D2a, EXT1)
	).


add_subsuming(  _ProcInfo, _HLDS, ALIAS, [], [ALIAS]).
add_subsuming(  ProcInfo, HLDS, ALIAS, [ A | R ], RESULT ):-
	(
		less_or_equal( ProcInfo, HLDS, ALIAS,A)
	->
		RESULT = [ A | R ]
	;
		less_or_equal( ProcInfo, HLDS, A, ALIAS)
	->
		add_subsuming( ProcInfo, HLDS, ALIAS, R, RESULT)
		% RESULT = [ ALIAS | R ] 
	;
		add_subsuming(  ProcInfo, HLDS, ALIAS, R, TEMP),
		RESULT = [ A | TEMP ]
	).

least_upper_bound_lists(ProcInfo, HLDS, L1, L2, L):-
	list__foldl(pa_alias__add_subsuming(ProcInfo, HLDS), 
			L1, L2, L).

extend( ProcInfo, HLDS, NEW, OLD,  RESULT) :-
% 	alias_altclosure( ProcInfo, HLDS, NEW, OLD, RESULT).
	altclosure_altclos( HLDS, ProcInfo, NEW, OLD, RESULT). 

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- type altclos_path ---> undirected(alias)	% can be rotated
			; directed(alias).	% fixed order: shortcut of
						% path(alias, ... , alias)

:- pred alias_to_altclos_path(alias::in, altclos_path::out) is det.
alias_to_altclos_path(Alias, undirected(Alias)). 

:- pred altclos_path_to_alias(altclos_path::in, alias::out) is det.
altclos_path_to_alias( undirected(Alias), Alias ).
altclos_path_to_alias( directed(Alias), Alias ). 

%-----------------------------------------------------------------------------%

% altclos computations. 

	% altclosure_altclos( ModuleInfo, ProcInfo, NEW, OLD, RESULT)
	% computes the alternating closure of two lists of aliases.
	% RESULT = NEW + OLD + path2(NEW,OLD) + path3(NEW,OLD).
	% where path2(NEW,OLD) is: (a,b), such that (a,c) in NEW, 
	%				  and       (c,b) in OLD
	% where path3(NEW,OLD) is: (a,b), such that (a,c) in NEW,
	%					    (c,d) in OLD,
	%					    (d,b) in NEW
	% taking into account termshifts.
:- pred altclosure_altclos( module_info::in, proc_info::in, 
			list(alias)::in, list(alias)::in, 
			list(alias)::out ) is det.
altclosure_altclos( ModuleInfo, ProcInfo, NewAliases, OldAliases,
			ComputedAliases ):-
	(
		NewAliases = []
	->
		ComputedAliases = OldAliases
	;
		OldAliases = []
	-> 
		ComputedAliases = NewAliases
	; 
		altclosure_altclos_path2_3( ModuleInfo, ProcInfo, 
			NewAliases, OldAliases, 
			Path2, Path3), 
		list__foldl(
			pa_alias__least_upper_bound_lists(ProcInfo, ModuleInfo),
				[OldAliases,NewAliases,Path2,Path3],
				[],
				ComputedAliases)
	).

	% altclosure_altclos_path2_3( NewAliases, OldAliases, Path2, Path3)
:- pred altclosure_altclos_path2_3( module_info::in, proc_info::in, 
		list(alias)::in, list(alias)::in, 
		list(alias)::out, list(alias)::out) is det.
altclosure_altclos_path2_3( ModuleInfo, ProcInfo, 
				NewAliases, OldAliases, Path2, Path3):- 
	list__map( alias_to_altclos_path, NewAliases, StartPaths ), 
	list__foldl( 
		pred( StartPath::in, Acc::in, NewPaths::out) is det :-
		    (
			altclos_ordered_altclos_path( ModuleInfo, 
				ProcInfo, StartPath, 
				OldAliases, Acc, NewPaths)
		    ),
		StartPaths, 
		[],
		PathsLength2 ), 
	list__foldl(
		pred( StartPath::in, Acc::in, NewPaths::out) is det :-
		    (
			altclos_ordered_altclos_path( ModuleInfo, 
				ProcInfo, StartPath,
				NewAliases, Acc, NewPaths)
		    ),
		PathsLength2,
		[],
		PathsLength3), 
	list__map( altclos_path_to_alias, PathsLength2, Path2),
	list__map( altclos_path_to_alias, PathsLength3, Path3).

:- pred altclos_ordered_altclos_path( module_info::in, proc_info::in, 
		altclos_path::in, list(alias)::in, 
		list(altclos_path)::in, list(altclos_path)::out) is det.
altclos_ordered_altclos_path( ModuleInfo, ProcInfo, 
			StartPath, EndAliases, AccPaths, NewPaths):- 
	list__filter_map(single_altclos_path( ModuleInfo, ProcInfo, 
				StartPath ), 
				EndAliases, NewPaths0 ),
	list__append( NewPaths0, AccPaths, NewPaths). 

	% single_altclos_path( StartPath, EndAlias, NewPath). 
	% Find a path starting from StartPath and ending in EndAlias. 
	% EndAlias can always be rotated. StartPath can only be
	% rotated if it is a single path. 
:- pred single_altclos_path( module_info::in, proc_info::in, 
		altclos_path::in, alias::in, 
		altclos_path::out) is semidet.
single_altclos_path( ModuleInfo, ProcInfo, StartPath, EndAlias, NewPath) :- 
	(
		StartPath = undirected(StartAlias)
	-> 
		( 
			single_directed_altclos_path_verify(ModuleInfo,
				ProcInfo, StartAlias,
				EndAlias, NewPath0)
		->
			NewPath = NewPath0
		; 
			switch(StartAlias, StartAliasSW),
			single_directed_altclos_path_verify(ModuleInfo,
				ProcInfo, StartAliasSW, 
				EndAlias, NewPath)
		)
	;
		StartPath = directed(StartAlias),
		single_directed_altclos_path_verify(ModuleInfo,
				ProcInfo, StartAlias, 
			EndAlias, NewPath)
	).

	% single_directed_altclos_path_verify( StartAlias, EndAlias, NewPath).
	% Compute a path starting from StartAlias to EndAlias. StartAlias
	% may not be rotated. EndAlias can be rotated if needed. The middle
	% alias still has to be verified. 
:- pred single_directed_altclos_path_verify( module_info::in, 
		proc_info::in, alias::in, alias::in, 
		altclos_path::out) is semidet.
single_directed_altclos_path_verify( ModuleInfo, ProcInfo, 
					StartAlias, EndAlias, Path ) :- 
	StartAlias = _StartDatastructure1 - StartDatastructure2, 
	EndAlias = EndDatastructure1 - EndDatastructure2, 
	(
		pa_datastruct__same_vars( StartDatastructure2,
					EndDatastructure1)
	->
		single_directed_altclos_path( ModuleInfo, ProcInfo, 
				StartAlias, EndAlias, 
				Path)
	; 
		pa_datastruct__same_vars( StartDatastructure2, 
					EndDatastructure2), 
		switch( EndAlias, EndAliasSW ), 
		single_directed_altclos_path( ModuleInfo, ProcInfo, 
				StartAlias, EndAliasSW, 
				Path)
	).

	% single_directed_altclos_path( StartAlias, EndAlias, NewPath).
	% they already have matching middle vars. 
:- pred single_directed_altclos_path( module_info::in, proc_info::in, 
			alias::in, alias::in, 
			altclos_path::out) is semidet.
single_directed_altclos_path( ModuleInfo, ProcInfo, 
				StartAlias, EndAlias, NewPath):-
	StartAlias = StartDatastructure1 - StartDatastructure2, 
	EndAlias = EndDatastructure1 - EndDatastructure2, 
	pa_datastruct__get_selector(StartDatastructure2, StartSelector), 
	pa_datastruct__get_var( StartDatastructure2, Var),
	pa_datastruct__get_selector(EndDatastructure1, EndSelector), 

	proc_info_vartypes( ProcInfo, VarTypes ), 
	map__lookup( VarTypes, Var, CommonVarType), 
	
	(
		% either EndSelector <= StartSelector
		%pa_selector__less_or_equal( EndSelector, StartSelector, 
		%			Ext)
		pa_selector__less_or_equal(ModuleInfo, 
					EndSelector, StartSelector, 
					CommonVarType, Ext)
	-> 
		% StartSelector.Ext = EndSelector, and StartAlias has
		% to be termshifted:
		pa_datastruct__termshift(StartDatastructure1, Ext, 
				NewStartDatastructure1),
		NewPath = directed( NewStartDatastructure1 -  
				EndDatastructure2 )
	;
		% or StartSelector <= EndSelector
		%pa_selector__less_or_equal( StartSelector, EndSelector, 
		%			Ext)
		pa_selector__less_or_equal(ModuleInfo,
					StartSelector, EndSelector, 
					CommonVarType, Ext)
	->
		% EndSelector.Ext = StartSelector, and EndAlias has to
		% be termshifted:
		pa_datastruct__termshift(EndDatastructure2, Ext, 
				NewEndDatastructure2), 
		NewPath = directed(StartDatastructure1 - NewEndDatastructure2)
	;
		fail
	).


%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred number_args( list(prog_var), list(pair(int, prog_var))).
:- mode number_args( in, out) is det.

number_args( ARGS, NUMBEREDARGS ) :- 
	list__map_foldl( 
		pred( A::in, AP::out, Nin::in, Nout::out) is det:- 
		    (
			AP = std_util:'-'(Nin, A),
			Nout = Nin + 1
		    ),
		ARGS,
		NUMBEREDARGS,
		1, _ ).
	
from_unification( _ProcInfo, _HLDS, 
		construct( VAR, CONS, ARGS0, _, _, _, _ ), _Info, AS ) :-
	get_rid_of_damn_typeinfos(CONS,ARGS0, ARGS),
	number_args( ARGS, NUMBEREDARGS), 
	list__foldl( alias_from_unif(VAR,CONS),NUMBEREDARGS, [], AS).

:- pred get_rid_of_damn_typeinfos( cons_id::in, list(prog_var)::in, 
			list(prog_var)::out) is det. 
get_rid_of_damn_typeinfos( Cons, Args0, Args ) :- 
	cons_id_maybe_arity( Cons, MaybeArity ), 
	(
		MaybeArity = yes( RealArity )
	-> 
		list__length( Args0, PseudoArity),
		(
			RealArity = PseudoArity
		-> 
			Args = Args0
		;
			Diff = PseudoArity - RealArity,
			(
				list__drop( Diff, Args0, Args1 )
			->
				Args = Args1
			; 	
				require__error("Blabla")
			)
		)	
	;
		Args = Args0
	).
	

from_unification( _ProcInfo, _HLDS, 
		deconstruct( VAR, CONS, ARGS0, _, _, _ ), Info, AS) :-
	get_rid_of_damn_typeinfos( CONS, ARGS0, ARGS), 
	number_args( ARGS, NUMBEREDARGS),
	optimize_for_deconstruct(NUMBEREDARGS, Info, ReducedARGS),
	list__foldl( alias_from_unif(VAR,CONS),ReducedARGS, [], AS).

:- pred optimize_for_deconstruct(
		list(pair(int, prog_var)), hlds_goal_info, 
		list(pair(int, prog_var))).
:- mode optimize_for_deconstruct(in, in, out) is det.
	% For deconstructions, a huge optimization can be made by
	% avoiding the construction of aliases involving variables 
	% which are not used anyway.
/*************************************************************
optimize_for_deconstruct(Args, _Info, Args).
*************************************************************/
optimize_for_deconstruct(Args, Info, ReducedArgs) :- 
	% Of all the args of a deconstruct, only the ones that are
	% in the pre-birth set are actually used during the subsequent
	% part of the code. Therefore, instead of creating aliases
	% between the deconstructed var and all the args of the
	% deconstruction, it is enough to consider only those with 
	% the args which are in pre-birth. 
	hlds_goal__goal_info_get_pre_births(Info, PreB),
	% keep_only_the_prebirths( Args, [], ReducedArgs, PreB ).
	keep_only_the_prebirths_v2( PreB, Args, ReducedArgs).
/*************************************************************
	list__filter(
		pred( NumVar::in ) is semidet :- 
			( NumVar = std_util:'-'(_, Var),
			  set__member( Var, PreB ) ),
		Args, 
		ReducedArgs).
*************************************************************/

:- pred keep_only_the_prebirths( list(pair(int, prog_var)), 
		list(pair(int, prog_var)), 
		list(pair(int, prog_var)), 
		set(prog_var)).
:- mode keep_only_the_prebirths( in, in, out, in) is det.

keep_only_the_prebirths( TODO, ACC, RES, PREB ) :- 
	(
		TODO = [ X | Xs ]
	->
		X = std_util:'-'(_, Var), 
		(
			set__remove( PREB, Var, PREB_1)
		->
			ACC_1 = [ X | ACC ],
			keep_only_the_prebirths( Xs, ACC_1, RES, PREB_1)
		;
			keep_only_the_prebirths( Xs, ACC, RES, PREB)
		)
	;
		RES = ACC 
	).

:- pred keep_only_the_prebirths_v2( set( prog_var), 
		list(pair(int, prog_var)),
		list(pair(int, prog_var))).
:- mode keep_only_the_prebirths_v2( in, in, out) is det.

keep_only_the_prebirths_v2( PreB, AllArgs, RES ) :- 
	set__to_sorted_list( PreB, ListPreB), 
	/** 
	% This length-test is not correct anymore in the presence 
	% of those *LLFD* typeinfos.
	list__length( ListPreB, L1), 
	list__length( AllArgs, L2), 

	(
		L1 = L2
	->
		RES = AllArgs
	;
	**/
	keep_only_the_prebirths_v2_2( ListPreB, AllArgs, [], RES).
	

:- pred keep_only_the_prebirths_v2_2( list(prog_var), 
		list(pair(int, prog_var)),
		list(pair(int, prog_var)),
		list(pair(int, prog_var))).
:- mode keep_only_the_prebirths_v2_2( in, in, in, out) is det.

keep_only_the_prebirths_v2_2( PreB, AllArgs, ACC, RES):-
	(
		PreB = [ X | Xs ]
	->
		( 
			list_find( X, Arg, AllArgs, AllArgs0)
		-> 
			ACC0 = [ Arg | ACC ],
			AllArgs1 = AllArgs0
		; 
			ACC0 = ACC,
			AllArgs1 = AllArgs
		), 
		keep_only_the_prebirths_v2_2( Xs, AllArgs1, ACC0, RES)
	;
		RES = ACC
	).

:- pred list_find( prog_var, pair(int, prog_var), 
			list(pair(int, prog_var)), 
			list(pair(int, prog_var))).
:- mode list_find( in, out, in, out) is semidet.

list_find( Var, Arg, Lin, Lout) :-
	Lin = [ First | Rest ],
	(
		First = std_util:'-'(_, Var)
	->
		Arg = First,
		Lout = Rest
	;
		list_find( Var, Arg, Rest, Tmp), 
		Lout = [ First | Tmp ]
	).
			

from_unification( ProcInfo, HLDS, 
		assign(VAR1,VAR2), _, AS):-
	(
		is_of_a_primitive_type(ProcInfo, HLDS, VAR1)
	->
		AS = []
	;
		pa_datastruct__init(VAR1,D1),
		pa_datastruct__init(VAR2,D2),
		ALIAS = D1 - D2,
		AS = [ALIAS]
	).

from_unification( _ProcInfo, _HLDS, 
		simple_test(_A,_B), _, AS):-
	AS = [].

from_unification( _ProcInfo, _HLDS, 
		complicated_unify(_,_,_), _, AS):-
	% XXXX only if partially instantiated datastructures cannot
	% exist.
	AS = [].

:- pred is_of_a_primitive_type(proc_info, module_info, prog_var).
:- mode is_of_a_primitive_type(in,in,in) is semidet.

is_of_a_primitive_type(ProcInfo, HLDS, VAR):-
	proc_info_vartypes( ProcInfo, VarTypes ),
	map__lookup( VarTypes, VAR, VarType ), 
	type_util__type_is_atomic(VarType, HLDS).

:- pred alias_from_unif(prog_var, cons_id, pair(int, prog_var), 
				list(alias),
				list(alias)).
:- mode alias_from_unif(in, in, in, in, out) is det.
alias_from_unif( VAR, CONS, N - ARG, LISTin, LISTout):-
	pa_datastruct__init( VAR, CONS, N, D1),
	pa_datastruct__init( ARG, D2 ),
	ALIAS = D1 - D2,
	LISTout = [ALIAS | LISTin].

	% switch the order of the alias...
:- pred switch(alias,alias).
:- mode switch(in,out) is det.

switch( D1 - D2, D2 - D1 ).
	
%-----------------------------------------------------------------------------%
% NORMALIZATION WITH TYPE INFORMATION
%-----------------------------------------------------------------------------%

normalize_wti(ProcInfo, HLDS, A0, A):-
	A0 = Da0 - Db0,
	% the two datastructs are normalized independently! 
	pa_datastruct__normalize_wti(ProcInfo, HLDS, Da0, Da),
	pa_datastruct__normalize_wti(ProcInfo, HLDS, Db0, Db),
	A = Da - Db.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

live_from_in_use(IN_USE, ALIASES, LIVE):-
	% filter the list of aliases, keeping only the ones that 
	% involve at least one variable from the IN_USE set
	list__filter_map(
		pa_alias__contains_one_of_vars(IN_USE),
		ALIASES,
		DATASTRUCTS),
	sr_live__from_datastructs(DATASTRUCTS, LIVE).

live_from_live0(ModuleInfo, ProcInfo, LIVE_0, ALIASES, LIVE):- 
	(
		(sr_live__top(LIVE_0) ; sr_live__bottom(LIVE_0))
	->
		LIVE = LIVE_0
	;
		sr_live__get_datastructs(LIVE_0, Datastructs),
		list__map(
			pa_alias__one_of_vars_is_live(ModuleInfo,
				ProcInfo, Datastructs),
			ALIASES,
			LL_DATASTRUCTS), 
		list__condense(LL_DATASTRUCTS, DATASTRUCTS),
		sr_live__from_datastructs(DATASTRUCTS, LIVE)
	).

	% one_of_vars_is_live(LIST, ALIAS, X^sx1)
	% returns true if
	% 	ALIAS = X^sx - Y^sy
	%   and Y^s1 \in LIST and
	%		sy = s1.s2 => sx1 = sx
	% 	   or
	%		sy.s2 = s1 => sx1 = sx.s2
:- pred one_of_vars_is_live(module_info, proc_info, 
				list(pa_datastruct__datastruct), 
				alias, 
				list(pa_datastruct__datastruct)).
:- mode one_of_vars_is_live(in, in, in, in, out) is det.

one_of_vars_is_live(ModuleInfo, ProcInfo, LIST, ALIAS, List_Xsx1) :- 
	one_of_vars_is_live_ordered(ModuleInfo, ProcInfo, LIST, ALIAS, L1), 
	switch(ALIAS, ALIASsw),	
	one_of_vars_is_live_ordered(ModuleInfo, ProcInfo, LIST, ALIASsw, L2),
	list__append(L1,L2, List_Xsx1).

:- pred one_of_vars_is_live_ordered( module_info, proc_info,
				list(pa_datastruct__datastruct),
				alias,
				list(pa_datastruct__datastruct) ).
:- mode one_of_vars_is_live_ordered( in, in, in, in, out) is det.

one_of_vars_is_live_ordered( ModuleInfo, ProcInfo, LIST, ALIAS, List_Xsx1 ) :- 
	ALIAS = Xsx - Ysy,
	pa_datastruct__get_var(Ysy, Y),
	list__filter( 
		pred( D::in ) is semidet :-
			( pa_datastruct__get_var(D,Y) ),
		LIST,
		Y_LIST),
	(
		% first try to find one of the found datastructs which is 
		% fully alive: so that Ysy is less or equal to at least one
		% Ys1 in Y_LIST (sy = s1.s2)
		list__filter(
			pred( Ys1::in ) is semidet :-
			    ( pa_datastruct__less_or_equal( ModuleInfo, 
					ProcInfo, Ysy, Ys1, _s2) ),
			Y_LIST,
			FY_LIST),
		FY_LIST = [_|_]
	->
		Xsx1 = Xsx,
		List_Xsx1 = [Xsx1]
	;
		% find all datastructs from Y_LIST which are less or 
		% equal to Ysy, select the one with the shortest selector
		% (note that there should be only one solution. if more
		% than one such datastruct is found, the initial live_set
		% is not minimal, while this should be somehow guaranteed).
		list__filter_map(
			pred( Ys1::in, S2::out) is semidet :-
			    ( pa_datastruct__less_or_equal( ModuleInfo, 
					ProcInfo, Ysy, Ys1, S2)),
			Y_LIST,
			SELECTOR_LIST),
		% each sx1 = sx.s2, where s2 is one of SELECTOR_LIST
		list__map(
			pred( S2::in, Xsx1::out) is det :-
			    ( pa_datastruct__termshift(Xsx, S2, Xsx1 ) ),
			SELECTOR_LIST,
			List_Xsx1 )
	).
			
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

apply_widening( ModuleInfo, ProcInfo, Alias0, Alias) :-
	Alias0 = Da0 - Db0, 
	apply_widening( ModuleInfo, ProcInfo, Da0, Da), 
	apply_widening( ModuleInfo, ProcInfo, Db0, Db), 
	Alias = Da - Db. 

apply_widening_list(ModuleInfo, ProcInfo, AliasList0, AliasList) :- 
	list__foldl(
		pred( Alias0::in, List0::in, List::out ) is det :- 
		    (
			apply_widening( ModuleInfo, ProcInfo, Alias0, 
					Alias), 
			add_subsuming(ProcInfo, ModuleInfo, Alias, 
					List0, List )
		    ),
		AliasList0, 
		[],
		AliasList ). 
		

