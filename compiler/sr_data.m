%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_data
% Main authors: nancy
% 
% The data structures which are shared between the various phases of the
% structure reuse analysis.
%
%-----------------------------------------------------------------------------%

:- module sr_data.
:- interface.

:- import_module map, set, std_util, list, io, term.
:- import_module pa_alias_as, pa_datastruct.
:- import_module sr_live.
:- import_module hlds_goal, hlds_pred, hlds_module, prog_data.

	% The information placed in the goal info which is used by
	% structure reuse.
	% This field should be initilaised to empty.
	% The sr_dead module replaces empty with choice.
	% The sr_choice module replaces choice with reuse.
:- type reuse_goal_info
	--->	empty
	;	choice(choice_info)
	;	reuse(short_reuse_info)
	.

:- type reuse_var == pair(prog_var, reuse_condition).
:- type choice_info
	--->	deconstruct(
				% The condition under which this cell
				% can be reused, if at all.
			maybe(reuse_condition)
		)
	;	construct(
				% The cells which could be reused by the
				% current construction unification and
				% the condition associated with reusing
				% that cell.
			set(reuse_var)
		)
	.

	% A reuse, whether direct or indirect, is only allowed as long
	% as the caller fulfills some conditions.  This type keeps track
	% of the information needed to verify whether the condition for
	% reuse is met or not. 
:- type reuse_condition
	--->	always
	;	condition(
		   nodes 		:: set(pa_datastruct__datastruct),
		   local_use_headvars 	:: set(prog_var),
		   local_alias_headvars :: alias_as 
		).

	% XXX this will replace the former tabled_reuse type. 
:- type memo_reuse == maybe(list(reuse_condition)).


%-----------------------------------------------------------------------------%
% reuse_condition predicates 
%-----------------------------------------------------------------------------%
:- pred reuse_condition_merge( reuse_condition::in, 
				reuse_condition::in,
				reuse_condition::out) is det.

:- pred reuse_condition_equal(reuse_condition, reuse_condition).
:- mode reuse_condition_equal(in, in) is semidet.

	% condition_init(Var, LFUi, LBUi, ALIASi, HVs, Condition).
:- pred reuse_condition_init(prog_var, set(prog_var), set(prog_var), 
		alias_as, list(prog_var), reuse_condition).
:- mode reuse_condition_init(in, in, in, in, in, out) is det.

	% rename the reuse condition given a map from FROM_VARS, to
	% TO_VARS
:- pred reuse_condition_rename( map(prog_var, prog_var), 
		reuse_condition, reuse_condition).
:- mode reuse_condition_rename( in, in, out ) is det.

	% print the reuse_condition 
:- pred reuse_condition_print( proc_info, reuse_condition, io__state, 
				io__state).
:- mode reuse_condition_print( in, in, di, uo) is det.

	% check whether the given live_set and alias_as satisfy
	% the condition for reuse. 
:- pred reuse_condition_verify( proc_info, module_info, 
			live_set, alias_as, set(prog_var), reuse_condition ).
:- mode reuse_condition_verify( in, in, in, in, in, in ) is semidet.

:- pred reuse_condition_update( proc_info, module_info, 
			set(prog_var), set(prog_var), 
			alias_as, list(prog_var), 
			reuse_condition, reuse_condition ).
:- mode reuse_condition_update( in, in, in, in, in, in, in, out) is det.

:- pred reuse_conditions_simplify( list(reuse_condition)::in, 
		list(reuse_condition)::out) is det.
%-----------------------------------------------------------------------------%
% memo_reuse predicates
%-----------------------------------------------------------------------------%

:- pred memo_reuse_equal( memo_reuse::in, memo_reuse::in) is semidet.
:- pred memo_reuse_init( memo_reuse::out ) is det.
:- pred memo_reuse_top( memo_reuse::in ) is semidet.
:- pred memo_reuse_rename( proc_info::in, list(prog_var)::in, 
		memo_reuse::in, memo_reuse::out) is det.
:- pred memo_reuse_rename( map(prog_var, prog_var)::in, memo_reuse::in,
		memo_reuse::out) is det.
:- pred memo_reuse_print( memo_reuse::in, sym_name::in, proc_info::in,
		io__state::di, io__state::uo) is det.
:- pred memo_reuse_parse( term(T)::in, memo_reuse::out, 
		maybe(sym_name)::out) is semidet.
:- pred memo_reuse_verify_reuse( proc_info::in, module_info::in, 
		memo_reuse::in, live_set::in, alias_as::in,
		set(prog_var)::in) is semidet.
:- pred memo_reuse_is_conditional( memo_reuse::in ) is semidet.
:- pred memo_reuse_is_unconditional( memo_reuse::in) is semidet.
:- pred memo_reuse_simplify( memo_reuse::in, memo_reuse::out) is det.
:- pred memo_reuse_merge( memo_reuse::in, memo_reuse::in, 
		memo_reuse::out) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module list, string, require, varset, bool.
:- import_module pa_datastruct, pa_alias_as.
:- import_module mercury_to_mercury, prog_out, prog_io, prog_io_util.
:- import_module sr_util.

reuse_condition_merge( C1, C2, C ):-
	(
		reuse_condition_equal( C1, C2 )
	->
		C = C1
	;
		reuse_condition_merge_2( C1, C2, C )
	).

:- pred reuse_condition_merge_2( reuse_condition::in, 
				reuse_condition::in,
				reuse_condition::out ) is det.

reuse_condition_merge_2( C1, C2, C) :- 
	(
		C1 = condition( N1, U1, A1 )
	->
		(
			C2 = condition( N2, U2, A2 )
		->
			set__union( N1, N2, N),
			set__union( U1, U2, U),
			pa_alias_as__add(A1, A2, A),
			C = condition( N, U, A )
		;
			% C2 = always
			C = C1
		)
	;
		% C1 = always
		C = C2
	).
			
			
reuse_condition_equal(always, always).
reuse_condition_equal(condition(NODES1, LU1, LA1), 
			condition(NODES2, LU2, LA2)):-
	set__equal(NODES1, NODES2),
	set__equal(LU1, LU2),
	pa_alias_as__equal(LA1, LA2).

reuse_condition_init(Var, LFUi, LBUi, ALIASi, HVs, CONDITION):- 
	% First determine the nodes to which the reuse is related. 
	% There are two cased:
	% 1. Var is a headvar, then it is sufficient to keep the topcel
	%    of that Var as only node. HeadVar-datastructures aliased
	%    to that node will still be retraceable at the moment 
	%    of verifying the condition
	% 2. Var is a local var, then we must compute all the headvar-
	%    datastructures aliased to the topcel of this var 
	%    (note that the aliases to some substructure of this var are
	%     not relevant for the nodes). All the obtained datastructures
	%    are the nodes for our condition. 
	pa_datastruct__init(Var, TopCel),
	(
		list__member(Var, HVs)
	->
		NODES = [TopCel]
	;
		pa_alias_as__collect_aliases_of_datastruct(TopCel, 
			ALIASi, AliasedData),
		list__filter(
			pred(DATA::in) is semidet :-
			  ( pa_datastruct__get_var(DATA,V), 
			    list__member(V, HVs) ),
			AliasedData,
			NODES)
	),
	(
		NODES = []
	->
		CONDITION = always
	;
		set__union(LFUi, LBUi, LUi),
		set__list_to_set(HVs, HVsSet),
		set__intersect(LUi, HVsSet, LUiHVs),
		pa_alias_as__project( HVs, ALIASi, LAiHVs),
		set__list_to_set(NODES, NODES_set),
		CONDITION = condition(NODES_set,LUiHVs, LAiHVs)
	).

reuse_condition_rename( Dict, Cin, Cout ) :- 
	(
		Cin = condition( Nodes, LUiH, LAiH )
	->
		% rename the nodes:
		set__to_sorted_list(Nodes, NodesList), 
		list__map(
			pa_datastruct__rename( Dict ),
			NodesList,
			RenNodesList),
		% rename the datastructures
		set__to_sorted_list(LUiH, ListLUiH),
		list__map(
			map__lookup( Dict ), 
			ListLUiH, 	
			ListRenLUiH ),
		set__list_to_set(ListRenLUiH, RenLUiH),
		% rename the alias
		pa_alias_as__rename( Dict, LAiH, RenLAiH ),
		set__list_to_set( RenNodesList, RenNodes ),
		Cout = condition(RenNodes, RenLUiH, RenLAiH )
	;
		Cout = Cin
	).

reuse_condition_print( _, always ) -->
	io__write_string("always").
reuse_condition_print( ProcInfo, condition(Nodes, LUiH, LAiH)) -->
	{ set__to_sorted_list( Nodes, NodesList ) }, 
	io__write_string("condition("),
		% write out the list of headvar-nodes involved
	io__write_string("["),
	io__write_list( NodesList, ",", 
			pred( D::in, IO1::di, IO2::uo) is det :- 
			    ( pa_datastruct__print(D, ProcInfo, IO1, IO2) )
			),
	io__write_string("], "),	

		% write out LUiH, list of prog_vars
	io__write_string("["),
	{ proc_info_varset(ProcInfo, ProgVarset) },
	{ set__to_sorted_list(LUiH, ListLUiH) },
	mercury_output_vars(ListLUiH, ProgVarset, bool__no), 
	io__write_string("], "),

		% write out LAiH, the aliases at the reuse-point
	pa_alias_as__print_aliases(LAiH, ProcInfo),	

	io__write_string(")").

reuse_condition_verify( _ProcInfo, _HLDS, _Live0, _Alias0, _Static, always).
reuse_condition_verify( ProcInfo, HLDS,  Live0, Alias0, Static,
		condition( Nodes, LUiH, LAiH ) ):- 

		% We cannot reuse a variable which was statically
		% constructed.
	list__filter_map(
		(pred(Node::in, Var::out) is semidet :-
			get_var(Node, Var),
			set__member(Var, Static)
		), set__to_sorted_list(Nodes), []),
	
	pa_alias_as__extend( ProcInfo, HLDS, Alias0, LAiH, Alias),
	pa_alias_as__live( LUiH, Live0, Alias, Live), 
	set__to_sorted_list(Nodes, NodesList), 
	list__filter(
		pred( D::in ) is semidet :- 
		    ( sr_live__is_live_datastruct(D, Live) ),
		NodesList,
		[] ).

:- import_module instmap. 

reuse_condition_update( _ProcInfo, _HLDS, 
		_LFUi, _LBUi, _ALIASi, _HVs, always, always ).
reuse_condition_update( ProcInfo, HLDS, LFUi, LBUi, ALIASi, HVs,
		condition( OLD_NODES_set, OLD_LUiH, OLD_LAiH ),
		CONDITION):- 
	set__to_sorted_list( OLD_NODES_set, OLD_NODES ), 
	list__map(
		pred(TOP::in,LIST::out) is det :- 
			( pa_alias_as__collect_aliases_of_datastruct(TOP, 
				ALIASi, LIST)),
		OLD_NODES,
		LISTS_ALL_NEW_NODES
		),
	list__condense( [ OLD_NODES | LISTS_ALL_NEW_NODES], ALL_NEW_NODES),
	list__filter(
		pred(DATA::in) is semidet :-
		  ( pa_datastruct__get_var(DATA,V), 
		    list__member(V, HVs) ),
		ALL_NEW_NODES,
		NEW_NODES),
	(
		NEW_NODES = []
	->
		CONDITION = always
	;
		% normalize all the datastructs
		list__map(
			pa_datastruct__normalize_wti( ProcInfo, HLDS ),
			NEW_NODES,
			NORM_NODES
			),
			% bit strange naming perhaps, but here the
			% OLD_LAiH has the role of `NEW' wrt the extension
			% operation.  
		pa_alias_as__extend( ProcInfo, HLDS, 
					OLD_LAiH, ALIASi, NewALIASi),
		pa_alias_as__project( HVs, NewALIASi, NEW_LAiH0),
			% XXX instmap here simply initialized, as currently
			% it's not used in the normalization anyway.. 	
		instmap__init_reachable(InstMap0), 
		pa_alias_as__normalize( ProcInfo, HLDS, InstMap0, 
				NEW_LAiH0, NEW_LAiH), 

		set__union(LFUi, LBUi, LUi),
		set__union(LUi, OLD_LUiH, NEW_LUi),
		set__list_to_set(HVs, HVsSet),
		set__intersect(NEW_LUi, HVsSet, NEW_LUiH),
		set__list_to_set( NORM_NODES, NORM_NODES_set), 
		CONDITION = condition( NORM_NODES_set, NEW_LUiH, NEW_LAiH )
	).


reuse_conditions_simplify( OLD, NEW ):- 
	list__foldl( 
		reuse_conditions_simplify_2, 
		OLD, 
		[],
		NEW). 

:- pred reuse_conditions_simplify_2(reuse_condition, 
		list(reuse_condition), list(reuse_condition)).
:- mode reuse_conditions_simplify_2(in,in,out) is det.

reuse_conditions_simplify_2( COND, ACC, NewACC) :-
	(
		COND = always
	->
		NewACC = ACC
	;
		list_ho_member(reuse_condition_equal, 
				COND, 
				ACC)
	->
		NewACC = ACC
	;
		NewACC = [ COND | ACC ]
	).
		

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
memo_reuse_equal(no, no).
memo_reuse_equal(yes(C1), yes(C2)):- 
	list__length(C1, L),
	list__length(C2, L), 
	list__filter(
		pred( COND::in ) is semidet :- 
		    (
			( sr_util__list_ho_member( reuse_condition_equal,
					COND, 	
					C1)
			-> 
				fail
			; 
				true
			)
		    ),
		C2, 
		[]).
			
memo_reuse_init(no).
memo_reuse_top(no).

memo_reuse_rename(ProcInfo, ActualVars, MEMOin, MEMOout ) :- 
	proc_info_headvars(ProcInfo, FormalVars),
	map__from_corresponding_lists( FormalVars, ActualVars, Dict),
	memo_reuse_rename( Dict, MEMOin, MEMOout).

memo_reuse_rename( Dict, TREUSEin, TREUSEout) :- 
	(
		TREUSEin = yes(CONDITIONS)
	->
		list__map(
			reuse_condition_rename( Dict ), 
			CONDITIONS, 
			RenCONDITIONS),
		TREUSEout = yes(RenCONDITIONS)
	;
		TREUSEout = TREUSEin
	).

memo_reuse_print( TREUSE, Name, ProcInfo ) --> 
	( 	
		{ TREUSE = yes(CONDS) }
	->
		io__write_string("yes(["),
		io__write_list(CONDS, ",", reuse_condition_print(ProcInfo)),
		io__write_string("], "),
		prog_out__write_quoted_sym_name(Name),
		io__write_string(")")
	;
		io__write_string("no")
	).

memo_reuse_parse( ReuseInformation, ParsedReuse, MaybeReuseName ) :- 
	(
		ReuseInformation = term__functor( term__atom("no"), _, _),
		MaybeReuseName = no,
		memo_reuse_init(ParsedReuse)
	;
		ReuseInformation = term__functor( term__atom("yes"),
					ReadConditions, _),
		conditions_list_parse( ReadConditions, Conditions, ReuseName),
		MaybeReuseName = yes(ReuseName),
		ParsedReuse = yes(Conditions)
	).

:- pred conditions_list_parse( list(term(T)),
		list(reuse_condition), sym_name).
:- mode conditions_list_parse( in, out, out ) is det.

conditions_list_parse( LISTTERM, CONDS, ReuseName ) :- 
	(
		LISTTERM = [ OneITEM , NameTerm ]
	->
		condition_rest_parse(OneITEM, CONDS),
		parse_qualified_term(NameTerm, NameTerm, "pragma reuse",
				Result),
		( Result = ok(ReuseName0, []) ->
			ReuseName = ReuseName0
		;
			error("(sr_data) conditions_list_parse: conditions_list_parse")
		)
	;
		list__length( LISTTERM, L ), 
		string__int_to_string(L, LS), 
		string__append_list( ["(sr_data) conditions_list_parse: ",
				"wrong number of arguments. yes/", LS,
				" should be yes/2"], Msg),
		error(Msg)
	).

:- pred condition_parse(term(T), reuse_condition).
:- mode condition_parse(in, out) is det.

condition_parse( TERM, COND ) :- 
	(
		TERM = term__functor( term__atom( CONS ), Args, _)
	->
		(
			CONS = "condition"	
		->
			(
				Args = [ NodesTerm, LUiHTerm, LAiHTerm ]
			->
				nodes_parse(NodesTerm, NodesList),
				set__list_to_set(NodesList, Nodes), 
				vars_parse(LUiHTerm, LUiH),
				pa_alias_as__parse_read_aliases_from_single_term( LAiHTerm, LAiH),
				COND = condition( Nodes, LUiH, LAiH )
			;
				list__length(Args, L),
				string__int_to_string( L, LS), 
				string__append_list( 
					[ "(sr_data) condition_parse: ",
					"wrong number of arguments. ",
					"condition/",LS, " should be ",
					"condition/3"], Msg),
				error(Msg)
			)
		;
			term__det_term_to_type( TERM, TYPE ),
			varset__init(V), 
			mercury_type_to_string(V, TYPE, StringTerm),
			string__append_list( 
				["(sr_data) condition_parse: ",
				"wrong constructur. `", 
				StringTerm, 
				"' should be `condition'"], Msg),
			error(Msg)
		)
	;
		error("(sr_data) condition_parse: term is not a functor")
	).

:- pred nodes_parse( term(T), list(pa_datastruct__datastruct)).
:- mode nodes_parse( in, out) is det.

nodes_parse( Term, Datastructs ) :- 
	(
		Term = term__functor( term__atom(CONS), Args, _)
	->
		(
			CONS = ".",
			Args = [ First , Rest ]
		->
			pa_datastruct__parse_term( First, D1),
			nodes_parse( Rest, D2),
			Datastructs = [ D1 | D2 ]
		;
			CONS = "[]"
		->
			Datastructs = []
		;
			string__append("(sr_data) nodes_parse: could not parse nodes, top cons: ", CONS, Msg),
			error(Msg)
		)
	;
		error("(sr_data) nodes_parse: term not a functor")
	).

:- pred vars_parse( term(T), set(prog_var)).
:- mode vars_parse( in, out) is det.

vars_parse( Term, Vars ) :- 
	vars_parse_list( Term, VarList) , 
	set__list_to_set( VarList, Vars).

:- pred vars_parse_list( term(T), list(prog_var)).
:- mode vars_parse_list( in, out) is det.

vars_parse_list( Term, Vars ) :- 
	(
		Term = term__functor( term__atom(CONS), Args, _)
	->
		(
			CONS = ".",
			Args = [ First , Rest ]
		->
			( 
				First = term__variable(V)
			->
				V1 = V
			;
				error("(sr_data) vars_parse_list: list should contain variables.")
			),	
			term__coerce_var(V1, PROGVAR),
			vars_parse_list( Rest, V2),
			Vars = [ PROGVAR | V2 ]
		;
			CONS = "[]"
		->
			Vars = []
		;
			string__append("(sr_data) vars_parse_list: could not parse nodes, top cons: ", CONS, Msg),
			error(Msg)
		)
	;
		error("(sr_data) vars_parse_list: term not a functor")
	).


:- pred condition_rest_parse(term(T), list(reuse_condition)).
:- mode condition_rest_parse(in, out) is det.

condition_rest_parse( Term, CONDS ) :- 
	(
		Term = term__functor( term__atom(CONS), Args, _)
	->
		(
			CONS = ".",
			Args = [ First , Rest ]
		->
			condition_parse( First, COND1),
			condition_rest_parse( Rest, COND2),
			CONDS = [ COND1 | COND2 ]
		;
			CONS = "[]"
		->
			CONDS = []
		;
			string__append("(sr_data) condition_rest_parse: could not parse conditions, top cons: ", CONS, Msg),
			error(Msg)
		)
	;
		error("(sr_data) condition_rest_parse: term not a functor")
	).

memo_reuse_verify_reuse( ProcInfo, HLDS, TREUSE, Live0, Alias0, Static ) :-
	TREUSE = yes(CONDITIONS), 
	list__takewhile( reuse_condition_verify( ProcInfo, HLDS, 
						Live0, Alias0, Static ), 
				CONDITIONS, _, [] ).

memo_reuse_is_conditional( yes([_|_]) ).
memo_reuse_is_unconditional( yes([]) ).

memo_reuse_simplify(M0, M):-
	(
		M0 = yes( Conditions0 )
	->
		reuse_conditions_simplify( Conditions0, Conditions ),
		M = yes( Conditions )
	;
		M = M0
	).

memo_reuse_merge(M1, M2, M) :-
	(
		M1 = yes(L1)
	->
		(
			M2 = yes(L2)
		->
			list__append(L1, L2, L),
			M0 = yes(L)
		;
			M0 = M1
		)
	;
		M0 = M2
	),
	memo_reuse_simplify(M0, M).

