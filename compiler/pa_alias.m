%-----------------------------------------------------------------------------%
% Copyright (C) 1996-2000 The University of Melbourne.
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

:- type alias.

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
:- pred aliased_to( alias, datastruct, datastruct ).
:- mode aliased_to( in, in, out) is semidet.

	% Rename the variables of the alias using the given mapping. 
:- pred rename( map(prog_var, prog_var), alias, alias).
:- mode rename( in, in, out) is det.
/*  was before: 
:- pred rename_alias( map(prog_var, prog_var), alias, 
			list(alias), list(alias)).
:- mode rename_alias( in, in, in, out) is det.
*/

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
:- pred print( proc_info, string, string, alias, io__state, io__state).
:- mode print( in, in, in, in, di, uo) is det.

	% parsing routines
:- pred parse_term( term(T), alias).
:- mode parse_term( in, out) is det.

:- pred live_from_in_use(set(prog_var), list(alias), live_set).
:- mode live_from_in_use(in, in, out) is det.

:- pred live_from_live0(live_set, list(alias), live_set).
:- mode live_from_live0(in, in, out) is det.

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

:- type alias == pair(datastruct).

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

print( ProcInfo, FrontString, EndString, ALIAS ) -->
	{ ALIAS = D1 - D2 },
	io__write_string( FrontString ),
	io__write_string( "pair( " ),
	pa_datastruct__print( D1, ProcInfo ),
	io__write_string(" , "),
	pa_datastruct__print( D2, ProcInfo ),
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
	
aliased_to( Alias, Data1, Data2 ) :-
	Alias = D1 - D2,
	(
		pa_datastruct__less_or_equal(Data1, D1, EXT)
	->
		pa_datastruct__termshift(D2, EXT, Data2)
	;
		pa_datastruct__less_or_equal(Data1, D2, EXT)
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


less_or_equal( _ProcInfo, _HLDS, A1, A2 ) :-
	A1 = D1a - D1b,
	A2 = D2a - D2b,
	(
		% XXX TEST underscored extensions!
		pa_datastruct__less_or_equal(D1a,D2a, EXT1),
		pa_datastruct__less_or_equal(D1b,D2b, EXT1)
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
		pa_datastruct__less_or_equal(D1a,D2b, EXT1),
		pa_datastruct__less_or_equal(D1b,D2a, EXT1)
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

extend( ProcInfo, HLDS, OLD, NEW, RESULT) :-
	alias_altclosure( ProcInfo, HLDS, NEW, OLD, RESULT).

	% alias_altclosure( NEW, OLD, RESULT)
	% computes the alternating closure of two lists of aliases.
	% RESULT = NEW + OLD + path2(NEW,OLD) + path3(NEW,OLD).
	% where path2(NEW,OLD) is: (a,b), such that (a,c) in NEW, 
	%				  and       (c,b) in OLD
	% where path3(NEW,OLD) is: (a,b), such that (a,c) in NEW,
	%					    (c,d) in OLD,
	%					    (d,b) in NEW
	% taking into account termshifts.
:- pred alias_altclosure( proc_info, module_info, 
				list(alias),list(alias),list(alias)).
:- mode alias_altclosure( in, in, in,in,out) is det.

alias_altclosure( ProcInfo, HLDS, NEW, OLD, RESULT) :-
	(
		NEW = []
	->
		RESULT = OLD
	;
		OLD = []
	->
		RESULT = NEW
	;
		altclosure_path2_3(NEW,OLD,PATH2,PATH3),
		% NEW is not necessaraly minimal wrt subsumption
		% OLD is guaranteed to be minimal
		% so the next foldl operation should have as a starting
		% point: OLD and not NEW ! 
		list__foldl(pa_alias__least_upper_bound_lists(ProcInfo,HLDS),
				[OLD,NEW,PATH2,PATH3],[],RESULT)
	).

:- pred altclosure_path2_3(list(alias),list(alias),list(alias),list(alias)).
:- mode altclosure_path2_3(in,in,out,out) is det.

altclosure_path2_3(NEW,OLD,PATH2,PATH3):-
		% not only this returns the path2 results,
		% but these results are also such that:
		% ALIAS =  D1 - D2, where D1 is from NEW, en D2
		% from OLD
		% constructs paths from NEW to OLD
	list__foldl(altclos_ordered_path(OLD),NEW,[],PATH2),
		% constructs paths from PATH2 (NEW -> OLD) to NEW
	list__foldl(altclos_ordered_path(NEW),PATH2,[],PATH3).


	% altclos_ordered_path( to_aliases, from_alias, temporary result,
	%						new result).
:- pred altclos_ordered_path(list(alias),alias,list(alias),list(alias)).
:- mode altclos_ordered_path(in,in,in,out) is det.

altclos_ordered_path( TO_LIST, FROM_ALIAS, LISTin, LISTout) :-
	list__filter_map(single_altclos(FROM_ALIAS),TO_LIST,NEW),
	list__append(NEW,LISTin,LISTout).

	% single_altclos( FROM_ALIAS, TO_ALIAS, RESULT_ALIAS).
	% --> semidet!
:- pred single_altclos(alias,alias,alias).
:- mode single_altclos(in,in,out) is semidet.

single_altclos( FROM , TO , RESULT ) :-
	FROM = DFa - DFb,
	TO   = DTa - DTb,
	(
		pa_datastruct__same_vars(DFb,DTa)
	-> 
		single_directed_altclos(FROM, TO, RESULT)
	;
		pa_datastruct__same_vars(DFa,DTa)
	->
		switch(FROM,FROMsw),
		single_directed_altclos(FROMsw,TO,RESULT)
	;
		pa_datastruct__same_vars(DFb,DTb)
	->
		switch(TO,TOsw),
		single_directed_altclos(FROM,TOsw,RESULT)
	;
		pa_datastruct__same_vars(DFa,DTb)
	->
		switch(FROM,FROMsw),
		switch(TO,TOsw),
		single_directed_altclos(FROMsw,TOsw,RESULT)
	;
		fail
	).

	% single_directed_altclos(FROM,TO, RESULT), with matching
	% middle vars!
:- pred single_directed_altclos(alias,alias,alias).
:- mode single_directed_altclos(in,in,out) is semidet.
		
single_directed_altclos( FROM, TO, RESULT) :-
	FROM = DFa - DFb,
	TO   = DTa - DTb,
	pa_datastruct__get_selector(DFb,SF),
	pa_datastruct__get_selector(DTa,ST),
	(
		pa_selector__less_or_equal(ST,SF,EXT1)
	->
		% SF.EXT1 = ST
		pa_datastruct__termshift(DFa,EXT1,DRa),
		RESULT = DRa - DTb
	;
		pa_selector__less_or_equal(SF,ST,EXT2)
	->
		% ST.EXT1 = SF
		pa_datastruct__termshift(DTb,EXT2,DRb),
		RESULT = DFa - DRb
	;
		fail
	).

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
		construct( VAR, CONS, ARGS, _, _, _, _ ), _Info, AS ) :-
	number_args( ARGS, NUMBEREDARGS), 
	list__foldl( alias_from_unif(VAR,CONS),NUMBEREDARGS, [], AS).

from_unification( _ProcInfo, _HLDS, 
		deconstruct( VAR, CONS, ARGS, _, _, _ ), Info, AS) :-
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
	list__length( ListPreB, L1), 
	list__length( AllArgs, L2), 
	(
		L1 = L2
	->
		RES = AllArgs
	;
		keep_only_the_prebirths_v2_2( ListPreB, AllArgs, [], RES)
	).

:- pred keep_only_the_prebirths_v2_2( list(prog_var), 
		list(pair(int, prog_var)),
		list(pair(int, prog_var)),
		list(pair(int, prog_var))).
:- mode keep_only_the_prebirths_v2_2( in, in, in, out) is det.

keep_only_the_prebirths_v2_2( PreB, AllArgs, ACC, RES):-
	(
		PreB = [ X | Xs ]
	->
		list_find( X, Arg, AllArgs, AllArgs0),
		ACC0 = [ Arg | ACC ],
		keep_only_the_prebirths_v2_2( Xs, AllArgs0, ACC0, RES)
	;
		RES = ACC
	).

:- pred list_find( prog_var, pair(int, prog_var), 
			list(pair(int, prog_var)), 
			list(pair(int, prog_var))).
:- mode list_find( in, out, in, out) is det.

list_find( Var, Arg, Lin, Lout) :-
	(
		Lin = [ First | Rest ]
	->
		(
			First = std_util:'-'(_, Var)
		->
			Arg = First,
			Lout = Rest
		;
			list_find( Var, Arg, Rest, Tmp), 
			Lout = [ First | Tmp ]
		)
	;
		require__error("(pa_alias) list_find: could not find prog_var in list of args.")
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
	
%-------------------------------------------------------------------%
% NORMALIZATION WITH TYPE INFORMATION
%-------------------------------------------------------------------%

normalize_wti(ProcInfo, HLDS, A0, A):-
	A0 = Da0 - Db0,
	pa_datastruct__normalize_wti(ProcInfo, HLDS, Da0, Da),
	pa_datastruct__normalize_wti(ProcInfo, HLDS, Db0, Db),
	A = Da - Db.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%

live_from_in_use(IN_USE, ALIASES, LIVE):-
	% filter the list of aliases, keeping only the ones that 
	% involve at least one variable from the IN_USE set
	list__filter_map(
		pa_alias__contains_one_of_vars(IN_USE),
		ALIASES,
		DATASTRUCTS),
	sr_live__from_datastructs(DATASTRUCTS, LIVE).

live_from_live0(LIVE_0, ALIASES, LIVE):- 
	(
		(sr_live__top(LIVE_0) ; sr_live__bottom(LIVE_0))
	->
		LIVE = LIVE_0
	;
		sr_live__get_datastructs(LIVE_0, Datastructs),
		list__map(
			pa_alias__one_of_vars_is_live(Datastructs),
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
:- pred one_of_vars_is_live(list(pa_datastruct__datastruct), 
				alias, 
				list(pa_datastruct__datastruct)).
:- mode one_of_vars_is_live(in, in, out) is det.

one_of_vars_is_live(LIST, ALIAS, List_Xsx1) :- 
	one_of_vars_is_live_ordered(LIST, ALIAS, L1), 
	switch(ALIAS, ALIASsw),	
	one_of_vars_is_live_ordered(LIST, ALIASsw, L2),
	list__append(L1,L2, List_Xsx1).

:- pred one_of_vars_is_live_ordered( list(pa_datastruct__datastruct),
				alias,
				list(pa_datastruct__datastruct) ).
:- mode one_of_vars_is_live_ordered( in, in, out) is det.

one_of_vars_is_live_ordered( LIST, ALIAS, List_Xsx1 ) :- 
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
			    ( pa_datastruct__less_or_equal(Ysy, Ys1, _s2) ),
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
			    ( pa_datastruct__less_or_equal(Ysy, Ys1, S2)),
			Y_LIST,
			SELECTOR_LIST),
		% each sx1 = sx.s2, where s2 is one of SELECTOR_LIST
		list__map(
			pred( S2::in, Xsx1::out) is det :-
			    ( pa_datastruct__termshift(Xsx, S2, Xsx1 ) ),
			SELECTOR_LIST,
			List_Xsx1 )
	).
			
