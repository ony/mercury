%-----------------------------------------------------------------------------%
% Copyright (C) 1996-2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% module sr_reuse: defines the datastructure reuse. This datastructure
%	is used to keep track of all datastructures for reuse, direct 
%	reuses and indirect reuses and the associated conditions for
%	reuse. 
% main author: nancy

:- module sr_reuse.

:- interface.

%-------------------------------------------------------------------%
%-- import_module 

% library modules
:- import_module io, set, list, term, map, std_util.

% compiler modules
:- import_module sr_live.
:- import_module prog_data.
:- import_module hlds_data.
:- import_module pa_alias_as.
:- import_module hlds_pred.
:- import_module hlds_module.

%-------------------------------------------------------------------%
%-- type definitions

:- type reuses.
:- type reuse_condition.

	% It's useless to table instances of type `reuses'. The type
	% `tabled_reuse' has the purpose of representing the minimal 
	% part of the reuses: i.e. the conditions for reuse. 
:- type tabled_reuse.

%-------------------------------------------------------------------%
%-- predicates

:- pred init(arity, proc_info,reuses).
:- mode init(in, in, out) is det.

:- pred empty(reuses).
:- mode empty(in) is semidet.

	% add_direct_reuse(Var, Cons, LIVEi, LFUi, LBUi, ALIASi, 
	%			ReusesIN, ReusesOUT).
	% Add one direct reuse to the initial reuses. The direct
	% reuse concerns the topcel of variable Var, where the 
	% constructor Cons is deconstructed. At the deconstruction there
	% is a set of vars in local forward use (LFUi), a set of vars
	% in local backward use (LBUi), a set of aliases (ALIASi),
	% information needed for expressing the correct conditions for
	% reuse. 
:- pred add_direct_reuse(prog_var, cons_id, set(prog_var), set(prog_var), 
		alias_as, reuses, reuses).
:- mode add_direct_reuse(in, in, in, in, in, in, out) is det.

	% add_indirect_reuse(PRED_PROC_ID, INDIRECT_CONDITIONS, 
	%			LFUi, LBUi, ALIASi, HeadVars,
	%			ReusesIN, ReusesOUT).
	% Add one indirect reuse, translating the initial conditions
	% (INDIRECT_CONDITIONS) to new ones, based on the available
	% local information (LFUi, LBUi, ALIASi, and HeadVars). 
	% Note that the indirect conditions must already be translated
	% in terms of the actual variables and not the formal ones. 
	% Note: ProcInfo and HLDS are needed as at some point a new
	% 	alias_as has to be computed (pa_alias_as__extend/5)
:- pred add_indirect_reuse(proc_info, module_info, 
		pred_id, proc_id, tabled_reuse, 
		set(prog_var), set(prog_var),
		alias_as, 
		reuses, reuses).
:- mode add_indirect_reuse(in, in, in, in, in, in, in, in, in, out) is det.

	% Combine all the different sets of reuses at the end of 
	% a disjunction, taking into account that some of the direct
	% reuses will have to be marked as local (outside a disjunction,
	% one cannot reuse datastructures concerning variables which are
	% purely local to the disjunction).
:- pred least_upper_bound_disjunction(set(prog_var), list(reuses),
					reuses).
:- mode least_upper_bound_disjunction(in, in, out) is det.

	% Direct reuses concerning variables which are not nonlocal are
	% set to local. 
:- pred convert_to_local(set(prog_var), reuses, reuses).
:- mode convert_to_local(in, in, out) is det.

	% Combine two sets of reuses.
:- pred least_upper_bound( reuses, reuses, reuses).
:- mode least_upper_bound( in, in, out) is det.

:- pred least_upper_bound_list( list(reuses), reuses).
:- mode least_upper_bound_list( in, out) is det.

% XXX not really convinced that these predicates are really needed in
% this shape. 
	% Not all constructors marked for reuse can really be reused. This
	% happens when no candidates for reuse exist. 
	% `filter_real_reuses' removes all the occurences of dead deconstructs
	% which do not have any candidates for reuse. 
%:- pred filter_real_reuses( reuses, reuses ).
%:- mode filter_real_reuses( in, out) is det.

	% From all the real reuses (the direct ones which have candidates, 
	% and the indirect ones), keep only those who impose conditions
	% on the caller. 
%:- pred filter_conditional_reuses( reuses, reuses ).
%:- mode filter_conditional_reuses( in, out) is det.

:- pred try_to_reuse( cons_id, reuses, prog_var, reuses).
:- mode try_to_reuse( in, in, out, out) is semidet.

:- pred compile_time_gc_cells(reuses::in, list(prog_var)::out) is det.

%-------------------------------------------------------------------%
%-- tabled_reuse

:- pred to_tabled_reuse( reuses, tabled_reuse). 
:- mode to_tabled_reuse( in, out) is det.

:- pred tabled_reuse_equal( tabled_reuse, tabled_reuse).
:- mode tabled_reuse_equal( in, in) is semidet.

:- pred tabled_reuse_init( tabled_reuse).
:- mode tabled_reuse_init( out ) is det.

:- pred tabled_reuse_top( tabled_reuse).
:- mode tabled_reuse_top( in ) is semidet.

	% used to print the reuse information to the interface
	% files. 
:- pred tabled_reuse_print( tabled_reuse, sym_name, proc_info,
		io__state, io__state).
:- mode tabled_reuse_print( in, in, in, di, uo) is det.

:- pred tabled_reuse_parse( term(T), tabled_reuse, maybe(sym_name)).
:- mode tabled_reuse_parse( in, out, out ) is semidet.

	% tabled_reuse_verify_conditions( ProcInfo, HLDS, 
	%				TREUSE, Live0, Alias0)
	% Verify whether the conditions for reuse are met given the
	% tabled conditions (tabled_reuse in fact), and the abstract
	% situation of the callers' environment:
	%	- live datastructures (Live0), datastructures that would
	% 	  have been live due to the caller's environment when 
	% 	  one would have performed a procedure-entry operation. 
	% 	- set of aliased datastructures (Alias0), idem, renamed
	%	  and projected unto the formal parameters. 
	% ProcInfo and the full HLDS are also needed as at some point
	% two alias_as's are extended wrt each other. 
:- pred tabled_reuse_verify_conditions( proc_info, module_info,
				tabled_reuse, live_set, alias_as).
:- mode tabled_reuse_verify_conditions( in, in, in, in, in) is semidet.

:- pred tabled_reuse_rename( proc_info, list(prog_var), tabled_reuse,
				tabled_reuse).
:- mode tabled_reuse_rename( in, in, in, out ) is det.

:- pred tabled_reuse_rename( map( prog_var, prog_var), tabled_reuse, 
				tabled_reuse).
:- mode tabled_reuse_rename( in, in, out ) is det.

	% The procedure contains reuse which requires we check
	% conditions before being able to use the reuse.  This implies
	% that we need to create a new version of the code.
:- pred contains_conditional_reuse(tabled_reuse::in) is semidet.
			
	% The procedure contains unconditional reuse.
:- pred contains_unconditional_reuse(tabled_reuse::in) is semidet.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
%-------------------------------------------------------------------%

:- implementation.

%-------------------------------------------------------------------%
%-- import_module 

% library modules
:- import_module map, int, require, bool.
:- import_module std_util.
:- import_module string, varset.

% compiler modules
:- import_module prog_out, prog_io, prog_io_util.
:- import_module pa_datastruct.
:- import_module mercury_to_mercury.

%-------------------------------------------------------------------%
%-- type definitions

	% reuses information contains information about direct reuses
	% and indirect reuses. 
	% * Direct reuses are reuses which can be done within the procedure
	% itself (a deconstruction of some datastructure, followed by
	% a construction with the same constructor).
	% * Indirect reuses consist of calls to procedures allowing some
	% sort of reuse within their body. 
:- type reuses ---> 
		reuses(
			list(prog_var), % real headvars for the procedure
					% we're working on. 
			direct_reuses, 
			indirect_reuses
		).

	% a direct reuse is said global when it is a candidate for reuse
	% within the given context. It is local when it is local to some
	% path where the datastructure available for reuse is not reachable
	% from the place to which the reuses-set belongs. 
:- type direct_reuses ---> 
		direct_reuses(
			global:: map(cons_id, list(direct_reuse)),
		 	local :: map(cons_id, list(direct_reuse))
			).
:- type indirect_reuses == list(indirect_reuse).

	% This type is used to represent direct reuses.
	% When created, the number of candidates of reusing the datastructure
	% is zero, only when matching constructions are encountered will 
	% this field become non-zero. Only reuses with non-zero 
	% candidates are true direct reuses. 
:- type direct_reuse --->
		direct( 
			var 		:: prog_var,
			cons		:: cons_id, 
			cond		:: reuse_condition,
			candidates 	:: int
			).
	% An indirect reuse simply consists of information about
	% which predicate allows the reuse-call (trace-information), 
	% and which conditions are now to be met. 
:- type indirect_reuse --->
		indirect(
			pred_proc_id, 
				% implicitly, the empty list means that
				% reuse is unconditional (see `always')
			list(reuse_condition)
			).

	% A reuse, whether direct or indirect, is only allowed as long
	% as the caller fulfills some conditions. 
	% This type keeps track of the information needed to verify
	% whether the condition for reuse is met or not. 
:- type reuse_condition --->
		always
	;	condition(
		   nodes 		:: list(pa_datastruct__datastruct),
		   local_use_headvars 	:: set(prog_var),
		   local_alias_headvars :: alias_as 
			).

:- type candidates == int.
				
%-------------------------------------------------------------------%
%-- predicates

% predicates around the `reuses' type

init( Arity, ProcInfo, R ) :- 
	proc_info_headvars(ProcInfo, HeadVars) ,
	list__length(HeadVars, PseudoArity) , 
	NumberOfTypeInfos = PseudoArity - Arity ,
	list_drop_det(NumberOfTypeInfos, HeadVars, RealHeadVars) ,
	HVS = RealHeadVars, 
	direct_reuses_init(DR),
	IR = [], 
	R = reuses( HVS, DR, IR ).

:- pred list_drop_det(int,list(T),list(T)).
:- mode list_drop_det(in,in,out) is det.

list_drop_det(Len,List,End):-
	(
		list__drop(Len,List,End0)
	->
		End = End0
	;
		End = List
	).

empty( R ) :- 
	R = reuses( _, DR, IR ),
	direct_reuses_is_empty(DR),
	IR = [].

add_direct_reuse(VAR, CONS, LFUi, LBUi, ALIASi, ReusesIN, ReusesOUT):-
	ReusesIN = reuses(HVS, DR_0, IR), 
	direct_reuse_init(VAR,CONS,LFUi, LBUi, ALIASi, HVS, Direct),
	direct_reuses_add_global_reuse(CONS, Direct, DR_0, DR),
	ReusesOUT = reuses(HVS, DR, IR).

add_indirect_reuse(ProcInfo, HLDS, 
		PRED_ID, PROC_ID, TREUSE, LFUi, LBUi, ALIASi, 
		ReusesIN, ReusesOUT):- 
	( 
		TREUSE = yes(OLD_CONDS)
	->
		ReusesIN  = reuses(HVS, DR, IR_0),
		indirect_reuse_init(ProcInfo, HLDS, PRED_ID, PROC_ID, 
					OLD_CONDS, LFUi, LBUi, ALIASi, 
					HVS, INDIRECT),
		IR = [ INDIRECT | IR_0 ],
		ReusesOUT = reuses(HVS, DR, IR)
	;
		ReusesOUT = ReusesIN
	).

least_upper_bound_disjunction( NonLocals, ListReuses, Reuses):-
	list__map(
		convert_to_local(NonLocals),
		ListReuses,
		NewListReuses),
	least_upper_bound_list( NewListReuses, Reuses ).

convert_to_local( NonLocals, ReusesIN, ReusesOUT ) :- 
	ReusesIN = reuses( HVS, DRin, IR), 
	direct_reuses_convert_to_local( NonLocals, DRin, DRout), 
	ReusesOUT = reuses( HVS, DRout, IR).
least_upper_bound( reuses(HVS, DR1, IR1), reuses(_, DR2, IR2), 
			reuses(HVS, DR, IR)) :-
	direct_reuses_least_upper_bound(DR1, DR2, DR), 
	list__append(IR1, IR2, IR).	

least_upper_bound_list( ReusesList, Reuses) :- 
	(
		ReusesList = [ First | Rest ]
	->
		list__foldl( least_upper_bound, Rest, First, Reuses )
	; 
		require__error("(sr_reuse) least_upper_bound_list: list is empty.")
	).

try_to_reuse( CONS_ID, ReusesIN, Var, ReusesOUT) :- 
	ReusesIN = reuses( HVS, DRin, IR),
	direct_reuses_try_to_reuse( CONS_ID, DRin, Var, DRout),
	ReusesOUT = reuses( HVS, DRout, IR).

	% remove all occurences of dead deconstructs which do not have
	% any candidates for reuse. 
:- pred filter_real_reuses( reuses, reuses ).
:- mode filter_real_reuses( in, out) is det.

filter_real_reuses( ReusesIN, ReusesOUT) :- 
	ReusesIN = reuses( HVS, DRin, IR), 
	direct_reuses_filter_real_reuses( DRin, DRout) ,
	ReusesOUT = reuses( HVS, DRout, IR).

:- pred filter_conditions( reuses, list(reuse_condition)).
:- mode filter_conditions( in, out) is det.
	% preconditions: the reuses must have been filtered and reduced
	% to real reuses (filter_real_reuses/2)
filter_conditions( ReusesIN, Conditions) :- 
	ReusesIN = reuses( _, DR, IR), 

		% filter the conditions from the direct reuses
	direct_reuses_to_conditions( DR, COND1),

		% filter the conditions from the indirct reuses
	list__map( 
		indirect_reuse_get_conds,
		IR, 
		LLCONDS),
	list__condense(LLCONDS, COND2),

		% put all the obtained conditions together
	list__append( COND1, COND2, COND), 
		
		% and now simplify the bunch (including removing the 
		% `always' conditions.  
	conditions_simplify(COND, Conditions).

%-------------------------------------------------------------------%

:- type tabled_reuse == maybe(list(reuse_condition)).

contains_conditional_reuse(yes([_ | _])).
contains_unconditional_reuse(yes([])).

to_tabled_reuse( ReusesIN, TabledReuse ):-
		% remove all the dead deconstructs which do not have
		% any candidates for reuse. 
	filter_real_reuses( ReusesIN, RealReuses ), 
	(
		sr_reuse__empty(RealReuses)
	->
		TabledReuse = no	% no reuses
	;
		filter_conditions( RealReuses, Conditions ),
		TabledReuse = yes(Conditions)
	).

	
tabled_reuse_equal(no,no).
	% precondition: there are no doubles within the given lists of
	% conditions. 
tabled_reuse_equal(yes(C1), yes(C2)):- 
	list__length(C1, L),
	list__length(C2, L), % same length
	list__filter(
		pred( COND::in) is semidet :- 
		    (
			( list_ho_member( reuse_condition_equal,
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

tabled_reuse_parse( ReuseInformation, ParsedReuse, MaybeReuseName ) :- 
	(
		ReuseInformation = term__functor( term__atom("no"), _, _),
		MaybeReuseName = no,
		sr_reuse__tabled_reuse_init(ParsedReuse)
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
			error("conditions_list_parse")
		)
	;
		list__length( LISTTERM, L ), 
		string__int_to_string(L, LS), 
		string__append_list( ["(sr_reuse) conditions_list_parse: ",
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
				nodes_parse(NodesTerm, Nodes),
				vars_parse(LUiHTerm, LUiH),
				pa_alias_as__parse_read_aliases_from_single_term( LAiHTerm, LAiH),
				COND = condition( Nodes, LUiH, LAiH )
			;
				list__length(Args, L),
				string__int_to_string( L, LS), 
				string__append_list( 
					[ "(sr_reuse) condition_parse: ",
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
				["(sr_reuse) condition_parse: ",
				"wrong constructur. `", 
				StringTerm, 
				"' should be `condition'"], Msg),
			error(Msg)
		)
	;
		error("(sr_reuse) condition_parse: term is not a functor")
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
			string__append("(sr_reuse) nodes_parse: could not parse nodes, top cons: ", CONS, Msg),
			error(Msg)
		)
	;
		error("(sr_reuse) nodes_parse: term not a functor")
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
				error("(sr_reuse) vars_parse_list: list should contain variables.")
			),	
			term__coerce_var(V1, PROGVAR),
			vars_parse_list( Rest, V2),
			Vars = [ PROGVAR | V2 ]
		;
			CONS = "[]"
		->
			Vars = []
		;
			string__append("(sr_reuse) vars_parse_list: could not parse nodes, top cons: ", CONS, Msg),
			error(Msg)
		)
	;
		error("(sr_reuse) vars_parse_list: term not a functor")
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
			string__append("(sr_reuse) condition_rest_parse: could not parse conditions, top cons: ", CONS, Msg),
			error(Msg)
		)
	;
		error("(sr_reuse) condition_rest_parse: term not a functor")
	).

		
tabled_reuse_init(no).		
tabled_reuse_top(no).		

tabled_reuse_print( TREUSE, Name, ProcInfo ) --> 
	( 	
		{ TREUSE = yes(CONDS) }
	->
		io__write_string("yes(["),
		io__write_list(CONDS, ",", reuse_condition_print(ProcInfo)),
		io__write_string("], "),
		prog_out__write_sym_name(Name),
		io__write_string(")")
	;
		io__write_string("no")
	).

tabled_reuse_verify_conditions( ProcInfo, HLDS, TREUSE, Live0, Alias0 ) :-
	TREUSE = yes(CONDITIONS), 
	list__takewhile( reuse_condition_verify( ProcInfo, HLDS, 
						Live0, Alias0 ), 
				CONDITIONS, _, [] ).

tabled_reuse_rename(ProcInfo, ActualVars, TREUSEin, TREUSEout ) :- 
	proc_info_headvars(ProcInfo, FormalVars),
	map__from_corresponding_lists( FormalVars, ActualVars, Dict),
	tabled_reuse_rename( Dict, TREUSEin, TREUSEout).

tabled_reuse_rename( Dict, TREUSEin, TREUSEout) :- 
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

%-------------------------------------------------------------------%
	

%-------------------------------------------------------------------%
% `direct_reuses'
%-------------------------------------------------------------------%
	
	% direct_reuses consists of two maps: one representing the
	% global reuses (the ones for which candidates can still be
	% found), and local reuses (the ones for which there cannot
	% be any candidates, as the scopes are not matching). 
	% Each of these maps is in fact a mapping from one cons_id, 
	% and a list of direct-reuses, i.e. places where such a cons_id
	% becomes available for reuse. 
	% IMPORTANT: these lists are ordered (first the smallest): 
	% 		(now called INVARIANT_DR_LIST)
	%	given D1, D2, two direct_reuse's 
	%	D1 < D2 if D1^candidates < D2^candidates. 

:- pred direct_reuses_init(direct_reuses).
:- mode direct_reuses_init(out) is det.
	% INVARIANT_DR_LIST holds
direct_reuses_init(direct_reuses(G,L)):-
	map__init(G),
	map__init(L).

:- pred direct_reuses_is_empty(direct_reuses).
:- mode direct_reuses_is_empty(in) is semidet.
	% INVARIANT_DR_LIST holds
direct_reuses_is_empty(direct_reuses(G,L)):-
	map__is_empty(G),
	map__is_empty(L).

:- pred direct_reuses_add_global_reuse(cons_id, direct_reuse, 
		direct_reuses, direct_reuses).
:- mode direct_reuses_add_global_reuse(in, in, in, out) is det.
	% Precondition: the given direct reuse must have zero
	% 	candidates, then: INVARIANT_DR_LIST holds
direct_reuses_add_global_reuse( CONS, DIRECT, DRS0, DRS ):- 
	DRS0 = direct_reuses( G0, L ),
	(
		map__search( G0, CONS, SimilarDIRECTS_0)
	->
		SimilarDIRECTS = [ DIRECT | SimilarDIRECTS_0 ],
		map__det_update( G0, CONS, SimilarDIRECTS, G )
	;
		map__det_insert( G0, CONS, [DIRECT], G )
	),
	DRS  = direct_reuses( G , L ).

:- pred direct_reuses_least_upper_bound(direct_reuses, direct_reuses,
					direct_reuses).
:- mode direct_reuses_least_upper_bound(in, in, out ) is det.

direct_reuses_least_upper_bound(  DR1, DR2, DR ) :- 
	DR1 = direct_reuses( G1, L1),
	DR2 = direct_reuses( G2, L2), 
	combine_direct_reuse_maps( G1, G2, G),
	combine_direct_reuse_maps( L1, L2, L),
	DR  = direct_reuses( G, L). 

:- pred direct_reuses_filter_real_reuses(direct_reuses, direct_reuses).
:- mode direct_reuses_filter_real_reuses(in, out) is det.

direct_reuses_filter_real_reuses( DRin, DRout ) :-
	DRin = direct_reuses( Gin, Lin), 
	map__keys(Gin, GlobalCONSIDS),
	list__foldl( direct_reuse_map_filter_real_reuses, 
			GlobalCONSIDS, Gin, Gout), 
	map__keys(Lin, LocalCONSIDS), 
	list__foldl( direct_reuse_map_filter_real_reuses,
			LocalCONSIDS, Lin, Lout),
	DRout = direct_reuses( Gout, Lout) .

:- pred direct_reuse_map_filter_real_reuses( cons_id, 
			map(cons_id, list(direct_reuse)),
			map(cons_id, list(direct_reuse))).
:- mode direct_reuse_map_filter_real_reuses( in, in, out) is det.

direct_reuse_map_filter_real_reuses( CONS, MAPin, MAPout) :- 
	map__lookup( MAPin, CONS, ListReuses),
	list__filter( 
		direct_reuse_has_candidates, 
		ListReuses, 
		Filtered), 
	(
		Filtered = []
	->
		map__delete( MAPin, CONS, MAPout)
	;
		map__det_update( MAPin, CONS, Filtered, MAPout)
	).
	

:- pred direct_reuses_convert_to_local(set(prog_var), direct_reuses,
					direct_reuses). 
:- mode direct_reuses_convert_to_local(in, in, out) is det.

direct_reuses_convert_to_local( NonLocals, DRin, DRout) :- 
	DRin = direct_reuses( Gin, Lin ), 
	map__keys(Gin, Conses),
	list__foldl2(
		direct_reuses_convert_to_local_2( NonLocals ), 
		Conses,
		Gin, Gout, Lin, Lout),
	DRout = direct_reuses( Gout, Lout).

:- pred direct_reuses_convert_to_local_2(set(prog_var), cons_id,
		map(cons_id, list(direct_reuse)), 
		map(cons_id, list(direct_reuse)),
		map(cons_id, list(direct_reuse)),
		map(cons_id, list(direct_reuse))).
:- mode direct_reuses_convert_to_local_2(in, in, in, out, in, out) is det.
direct_reuses_convert_to_local_2( NonLocals, GlobalCons, Gin, Gout, 
					Lin, Lout ):- 
	map__lookup( Gin, GlobalCons, ReuseList ), 
	direct_reuse_list_divide( NonLocals, ReuseList, GlobalList, LocalList),
	(
		GlobalList = []
	->
		map__delete( Gin, GlobalCons, Gout)
	;
		map__det_update( Gin, GlobalCons, GlobalList, Gout )
	),
	(
		LocalList = []
	->
		Lout = Lin
	;
		(
			map__search( Lin, GlobalCons, OldLocalList )
		->
				% for the local list, the invariant is
				% of no importance.
			list__append( LocalList, OldLocalList, NewLocalList),
			map__det_update( Lin, GlobalCons, 
					NewLocalList, Lout)
		;
			map__det_insert( Lin, GlobalCons, LocalList, Lout )
		)
	).
		
:- pred combine_direct_reuse_maps( map(cons_id, list(direct_reuse)),
				   map(cons_id, list(direct_reuse)),
				   map(cons_id, list(direct_reuse))). 
:- mode combine_direct_reuse_maps( in, in, out) is det.
	% pre-condition: for each input map, INVARIANT_DR_LIST holds
combine_direct_reuse_maps( MAP1, MAP2, RESULT ) :- 
	map__keys( MAP1, CONSes ),
	list__foldl(
		pred( CONS::in, MAPin::in, MAPout::out) is det :-
		    ( 
			map__lookup( MAP1, CONS, LIST1),
			(   map__search( MAPin, CONS, LIST2 )
		        ->  direct_reuse_list_merge(LIST1, LIST2, LIST),
			    map__det_update( MAPin, CONS, LIST, MAPout )
			;   map__det_insert( MAPin, CONS, LIST1, MAPout )
			)
		     ),
		CONSes,
		MAP2,
		RESULT).

:- pred direct_reuse_list_divide( set(prog_var), list(direct_reuse),
			list(direct_reuse), list(direct_reuse)).
:- mode direct_reuse_list_divide( in, in, out, out) is det.

direct_reuse_list_divide( NonLocals, ReuseList, GlobalList, LocalList):-
	list__filter(
		pred( DR::in ) is semidet :- 
			( direct_reuse_get_var(DR, VAR), 
			  set__member(VAR, NonLocals) ),
		ReuseList, 
		GlobalList, 
		LocalList).
			


:- pred direct_reuse_list_merge(list(direct_reuse), list(direct_reuse),
			list(direct_reuse)).
:- mode direct_reuse_list_merge(in, in, out) is det.
	% preconditions: both lists are ordered (INVARIANT_DR_LIST)
direct_reuse_list_merge( L1, L2, L ):- 
	direct_reuse_list_merge_simple( L1, L2, Ltmp),
	direct_reuse_list_order(Ltmp, L).

:- pred direct_reuse_list_merge_simple( list(direct_reuse), 
			list(direct_reuse), list(direct_reuse)).
:- mode direct_reuse_list_merge_simple( in, in, out) is det.

direct_reuse_list_merge_simple( L1, L2, L) :-
	list__foldl(
		direct_reuse_list_add_reuse,
		L1, 
		L2,
		L).

:- pred direct_reuse_list_add_reuse( direct_reuse, list(direct_reuse),
			list(direct_reuse)).
:- mode direct_reuse_list_add_reuse( in, in, out) is det.

direct_reuse_list_add_reuse( DR, LISTin, LISTout ) :- 
	(
		LISTin = [ DRin | RESTin ]
	->
		(
			direct_reuse_same_case(DR, DRin)
		->
			direct_reuse_get_candidates(DR, CAND),
			direct_reuse_update_candidates(DRin, CAND, DRout),
			LISTout = [ DRout | RESTin ]
		;
			direct_reuse_list_add_reuse(DR, RESTin, RESTout),
			LISTout = [ DRin | RESTout ]
		)
	;
		LISTout = [ DR ] 
	).

:- pred direct_reuse_list_order( list(direct_reuse), list(direct_reuse)).
:- mode direct_reuse_list_order( in, out ) is det.

direct_reuse_list_order( Lin, Lout ) :- 
	list__sort( direct_reuse_compare, Lin, Lout ).

:- pred direct_reuses_try_to_reuse( cons_id, direct_reuses, prog_var, 
						direct_reuses).
:- mode direct_reuses_try_to_reuse( in, in, out, out) is semidet.

direct_reuses_try_to_reuse( CONS_ID, DRsIN, Var, DRsOUT ) :- 
	DRsIN = direct_reuses( Gin, L),
	map__keys( Gin, ALL_CONSES), 
	select_most_matching_cons( ALL_CONSES, CONS_ID, SELECTED_CONS_ID), 
	map__lookup( Gin, SELECTED_CONS_ID, LIST_REUSES_in),
	direct_reuse_list_try_to_reuse( LIST_REUSES_in, Var, LIST_REUSES_out),
	map__det_update( Gin, SELECTED_CONS_ID, LIST_REUSES_out, Gout),
	DRsOUT = direct_reuses( Gout, L).

:- pred select_most_matching_cons( list(cons_id), cons_id, cons_id).
:- mode select_most_matching_cons( in, in, out ) is semidet.

select_most_matching_cons( LIST, C, MATCH ) :- 
	(
		list__member( C, LIST )
	->
		MATCH = C
	;
		% cons_id_arity(C, ARITY),
		% select_same_arity_cons( LIST, ARITY, MATCH)
		fail
	).

	% picks out the first cons_id occuring in the given list that
	% has the same arity as the given cons_id.	
:- pred select_same_arity_cons( list(cons_id), int, cons_id).
:- mode select_same_arity_cons( in, in, out) is semidet.

select_same_arity_cons( LIST, ARITY, MATCH ):-
	LIST = [ CONS | REST ], 
	(
		cons_id_arity( CONS, ARITY )
	->
		MATCH = CONS
	; 
		select_same_arity_cons( REST, ARITY, MATCH )
	).
	

:- pred direct_reuse_list_try_to_reuse( list(direct_reuse), prog_var, 
					list(direct_reuse) ).
:- mode direct_reuse_list_try_to_reuse( in, out, out) is semidet.

direct_reuse_list_try_to_reuse( Lin, Var, Lout) :- 
	(
		Lin = [ Fin | R ] 
	->
		direct_reuse_get_candidates(Fin, 0),
		direct_reuse_get_var(Fin, Var), 
		direct_reuse_update_candidates( Fin, 1, Fout ),
		direct_reuse_list_order( [Fout | R ], Lout)
	;
		Lout = Lin,
		require__error("(sr_reuse) direct_reuse_list_try_to_reuse: empty reuse list.")
	).	

:- pred direct_reuses_to_conditions( direct_reuses, list(reuse_condition)).
:- mode direct_reuses_to_conditions( in, out ) is det.

direct_reuses_to_conditions( DRin, Conditions) :- 
	DRin = direct_reuses( G, L),
	map__keys( G, GCONSes), 
	list__foldl(
		direct_reuse_map_to_conditions(G), GCONSes, [], COND1),
	map__keys( L, LCONSes), 
	list__foldl( 
		direct_reuse_map_to_conditions(L), LCONSes, COND1, 
		Conditions).

:- pred direct_reuse_map_to_conditions( map(cons_id, list(direct_reuse)),
					cons_id, list(reuse_condition),
					list(reuse_condition)).
:- mode direct_reuse_map_to_conditions( in, in, in, out) is det.

direct_reuse_map_to_conditions( MAP, CONS, AccIN, AccOUT ):- 
	map__lookup( MAP, CONS, LISTReuses), 
	list__foldl(
		pred( DR::in, Ain::in, Aout::out) is det :- 
		    ( 
			% just to be sure
			(
				direct_reuse_has_candidates(DR)
			->
				direct_reuse_get_cond(DR, COND),
				Aout = [COND | Ain ]
			;
				Aout = Ain
			)
		    ),
		LISTReuses, 	
		AccIN, 
		AccOUT).

			
		
%-------------------------------------------------------------------%
% `direct_reuse' 
%-------------------------------------------------------------------%
	
:- pred direct_reuse_init(prog_var,cons_id, set(prog_var), set(prog_var),
		alias_as, list(prog_var), direct_reuse).
:- mode direct_reuse_init(in, in, in, in, in, in, out) is det.

direct_reuse_init(Var, Cons, LFUi, LBUi, ALIASi, HVs, Direct):- 
	reuse_condition_init(Var, LFUi, LBUi, ALIASi, HVs, COND),
	Direct = direct(Var, Cons, COND, 0).

:- pred direct_reuse_get_var(direct_reuse, prog_var).
:- mode direct_reuse_get_var(in, out) is det.
direct_reuse_get_var(DR, DR^var).

:- pred direct_reuse_get_cons(direct_reuse, cons_id).
:- mode direct_reuse_get_cons(in, out) is det.
direct_reuse_get_cons(DR, DR^cons).

:- pred direct_reuse_get_cond(direct_reuse, reuse_condition).
:- mode direct_reuse_get_cond(in, out) is det.
direct_reuse_get_cond(DR, DR^cond).

:- pred direct_reuse_get_candidates(direct_reuse, int).
:- mode direct_reuse_get_candidates(in, out) is det.
direct_reuse_get_candidates(DR, DR^candidates).

:- pred direct_reuse_has_candidates(direct_reuse).
:- mode direct_reuse_has_candidates(in) is semidet.
direct_reuse_has_candidates(DR):- 
	not(DR^candidates = 0).

:- pred direct_reuse_update_candidates(direct_reuse, int, direct_reuse).
:- mode direct_reuse_update_candidates(in, in, out) is det.
direct_reuse_update_candidates(DR, C, DR^candidates := DR^candidates + C).

:- pred direct_reuse_compare( direct_reuse, direct_reuse, 
				comparison_result ).
:- mode direct_reuse_compare( in, in, out ) is det.
direct_reuse_compare( D1, D2, RESULT ) :- 
	direct_reuse_get_candidates( D1, CAND1),
	direct_reuse_get_candidates( D2, CAND2),
	( 
		CAND1 = CAND2
	->
		RESULT = (=)
	;
		CAND1 > CAND2
	->	
		RESULT = (>)
	;
		RESULT = (<)
	).

:- pred direct_reuse_same_case( direct_reuse, direct_reuse ).
:- mode direct_reuse_same_case( in, in) is semidet.

direct_reuse_same_case( D1, D2 ) :- 
	(
		direct_reuse_get_var(D1, V),
		direct_reuse_get_var(D2, V)
	->
		(
			direct_reuse_get_cons(D1,C),
			direct_reuse_get_cons(D2,C)
		->
			direct_reuse_get_cond( D1, Cond1),
			direct_reuse_get_cond( D2, Cond2),
			(
				reuse_condition_equal(Cond1, Cond2)
			->
				true
			;
				fail
			)
		;
			error("(sr_reuse) direct_reuse_same_case: vars are the same, but have different cons_id's.")
		)
	;
		fail
	).
		
				
	

%-------------------------------------------------------------------%
% `indirect_reuse' 
%-------------------------------------------------------------------%

:- pred indirect_reuse_init(proc_info, module_info, 
		pred_id, proc_id, list(reuse_condition), 
		set(prog_var), set(prog_var), alias_as, list(prog_var),
		indirect_reuse).
:- mode indirect_reuse_init(in, in, in, in,in,in,in,in,in, out) is det.

indirect_reuse_init(ProcInfo, HLDS, 
		PRED_ID, PROC_ID, OLD_CONDS, LFUi, LBUi, ALIASi, 
		HVs, INDIRECT):- 
	list__map( 
		reuse_condition_update(ProcInfo, HLDS, 
				LFUi, LBUi, ALIASi, HVs),
		OLD_CONDS,
		NEW_CONDS), 
	conditions_simplify(NEW_CONDS, CONDS),	
	PRED_PROC_ID = proc( PRED_ID, PROC_ID), 
	INDIRECT = indirect(PRED_PROC_ID, CONDS).

:- pred indirect_reuse_get_conds(indirect_reuse, list(reuse_condition)).
:- mode indirect_reuse_get_conds(in, out) is det.
indirect_reuse_get_conds( IR, Conditions ):- 
	IR = indirect(_, Conditions).
	

%-------------------------------------------------------------------%
% `condition' 
%-------------------------------------------------------------------%

	% condition_init(Var, LFUi, LBUi, ALIASi, HVs, Condition).
:- pred reuse_condition_init(prog_var, set(prog_var), set(prog_var), 
		alias_as, list(prog_var), reuse_condition).
:- mode reuse_condition_init(in, in, in, in, in, out) is det.

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
		CONDITION = condition(NODES,LUiHVs, LAiHVs)
	).

	% update an old reuse condition to the current context.
	% proc_info and module_info are needed in order to perform
	% pa_alias_as__extend (alternating closure).
:- pred reuse_condition_update(proc_info, module_info, 
		set(prog_var),set(prog_var),
		alias_as, list(prog_var), reuse_condition, reuse_condition).
:- mode reuse_condition_update(in, in, in,in,in,in,in, out) is det.

reuse_condition_update( _ProcInfo, _HLDS, 
		_LFUi, _LBUi, _ALIASi, _HVs, always, always ).
reuse_condition_update( ProcInfo, HLDS, LFUi, LBUi, ALIASi, HVs,
		condition( OLD_NODES, OLD_LUiH, OLD_LAiH ),
		CONDITION):- 
		% condition( NEW_NODES, NEW_LUiH, NEW_LAiH ) ):-
	list__map(
		pred(TOP::in,LIST::out) is det :- 
			( pa_alias_as__collect_aliases_of_datastruct(TOP, 
				ALIASi, LIST)),
		OLD_NODES,
		LISTS_ALL_NEW_NODES
		),
	list__condense(LISTS_ALL_NEW_NODES, ALL_NEW_NODES),
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
		pa_alias_as__project( HVs, NewALIASi, NEW_LAiH),
		set__union(LFUi, LBUi, LUi),
		set__union(LUi, OLD_LUiH, NEW_LUi),
		set__list_to_set(HVs, HVsSet),
		set__intersect(NEW_LUi, HVsSet, NEW_LUiH),
		CONDITION = condition( NORM_NODES, NEW_LUiH, NEW_LAiH )
	).
	
	
	
			

:- pred reuse_condition_equal(reuse_condition, reuse_condition).
:- mode reuse_condition_equal(in, in) is semidet.

reuse_condition_equal(always, always).
reuse_condition_equal(condition(NODES1, LU1, LA1), 
			condition(NODES2, LU2, LA2)):-
	set__list_to_set(NODES1, N1),
	set__list_to_set(NODES2, N2),
	set__equal(N1, N2),
	set__equal(LU1, LU2),
	pa_alias_as__equal(LA1, LA2).

	% Remove doubles, remove 'always' conditions.
:- pred conditions_simplify(list(reuse_condition), 
				list(reuse_condition)).
:- mode conditions_simplify(in,out) is det.

conditions_simplify( OLD, NEW ) :- 
	list__foldl(
		conditions_simplify_2, 
		OLD,
		[],
		NEW).

:- pred conditions_simplify_2(reuse_condition, 
		list(reuse_condition), list(reuse_condition)).
:- mode conditions_simplify_2(in,in,out) is det.

conditions_simplify_2( COND, ACC, NewACC) :-
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

:- pred list_ho_member(pred(T,T), T, list(T)).
:- mode list_ho_member(pred(in, in) is semidet, in, in) is semidet.

list_ho_member( EQUALITY_TEST, ELEMENT, LIST ) :- 
	LIST = [ HEAD | TAIL ],
	(
		EQUALITY_TEST(HEAD, ELEMENT)
	->
		true
	;	
		list_ho_member( EQUALITY_TEST, ELEMENT, TAIL )
	).

	% reuse_condition_verify( ProcInfo, HLDS, Live0, Alias0, CONDITION)
	% --> see tabled_reuse_verify_conditions/5
:- pred reuse_condition_verify( proc_info, module_info, 
			live_set, alias_as, reuse_condition ).
:- mode reuse_condition_verify( in, in, in, in, in ) is semidet.

reuse_condition_verify( _ProcInfo, _HLDS, _Live0, _Alias0, always).
reuse_condition_verify( ProcInfo, HLDS,  Live0, Alias0, 
		condition( Nodes, LUiH, LAiH ) ):- 
	pa_alias_as__extend( ProcInfo, HLDS, Alias0, LAiH, Alias),
	pa_alias_as__live( LUiH, Live0, Alias, Live), 
	list__filter(
		pred( D::in ) is semidet :- 
		    ( sr_live__is_live_datastruct(D, Live) ),
		Nodes,
		[] ).
		
:- pred reuse_condition_rename( map(prog_var, prog_var), 
		reuse_condition, reuse_condition).
:- mode reuse_condition_rename( in, in, out ) is det.

reuse_condition_rename( Dict, Cin, Cout ) :- 
	(
		Cin = condition( Nodes, LUiH, LAiH )
	->
		% rename the nodes:
		list__map(
			pa_datastruct__rename( Dict ),
			Nodes,
			RenNodes),
		% rename the datastructures
		set__to_sorted_list(LUiH, ListLUiH),
		list__map(
			map__lookup( Dict ), 
			ListLUiH, 	
			ListRenLUiH ),
		set__list_to_set(ListRenLUiH, RenLUiH),
		% rename the alias
		pa_alias_as__rename( Dict, LAiH, RenLAiH ),
		Cout = condition(RenNodes, RenLUiH, RenLAiH )
	;
		Cout = Cin
	).
	
:- pred reuse_condition_print( proc_info, reuse_condition, io__state, 
				io__state).
:- mode reuse_condition_print( in, in, di, uo) is det.

reuse_condition_print( _, always ) -->
	io__write_string("always").
reuse_condition_print( ProcInfo, condition(Nodes, LUiH, LAiH)) -->
	io__write_string("condition("),
		% write out the list of headvar-nodes involved
	io__write_string("["),
	io__write_list( Nodes, ",", 
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

	
%-------------------------------------------------------------------%

compile_time_gc_cells(reuses(_, DirectReuses, _), GcCells) :-
	GlobalDirectReuses = list__condense(map__values(DirectReuses ^ global)),
	LocalDirectReuses = list__condense(map__values(DirectReuses ^ local)),
	list__filter_map(compile_time_gc_canditate,
			GlobalDirectReuses `list__append` LocalDirectReuses,
			GcCells).

:- pred compile_time_gc_canditate(direct_reuse::in, prog_var::out) is semidet.

compile_time_gc_canditate(direct(Var, _, Cond, Canditates), Var) :-
	Canditates = 0,
	(
		Cond = always
	;
		Cond = condition([], _, _)
	).

%-------------------------------------------------------------------%
