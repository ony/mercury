%-----------------------------------------------------------------------------%
% Copyright (C) 1996-2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module sr_reuse_run: implements the process of annotating each procedure
%		 with reuse information, i.e. with information which
%		 states at which places reuse is allowed (direct +
%		 indirect) and what the conditions are for the caller
%		 of the particular procedures. 
% main author: nancy

:- module sr_reuse_run.

:- interface.

%-------------------------------------------------------------------%
%-- import_module

% library modules
:- import_module io.

% compiler modules
:- import_module hlds_module.

%-------------------------------------------------------------------%
%-- exported predicates

	% the main pass
:- pred sr_reuse_run__reuse_pass( module_info, module_info, 
					io__state, io__state).
:- mode sr_reuse_run__reuse_pass( in, out, di, uo) is det.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
:- implementation.

%-------------------------------------------------------------------%
%-- import_module

% library modules
:- import_module require.
:- import_module set, list, map, int.
:- import_module std_util, string.

% compiler modules
:- import_module dependency_graph.
:- import_module hlds_pred, hlds_goal, prog_data.
:- import_module special_pred, prog_util, prog_out.
:- import_module globals, options, passes_aux.
:- import_module type_util.

:- import_module pa_alias_as, pa_run.
:- import_module sr_reuse.
:- import_module sr_reuse_util.
:- import_module sr_live.

%-------------------------------------------------------------------%
%-- predicates

sr_reuse_run__reuse_pass( HLDSin, HLDSout ) -->
	{ HLDS0 = HLDSin },

		% strongly connected components needed
	{ module_info_ensure_dependency_info( HLDS0, HLDS1) },
	{ module_info_get_maybe_dependency_info( HLDS1, MaybeDepInfo) } ,
	(
		{ MaybeDepInfo = yes(DepInfo) }
	->
		{ hlds_dependency_info_get_dependency_ordering( DepInfo, DepOrdering ) },
		% perform the analysis, and annotate the procedures
		run_with_dependencies( DepOrdering, HLDS1, HLDSout) %,
	;
		{ error("(sr_reuse_run) reuse_pass: no dependency info") }
	).

:- pred run_with_dependencies( dependency_ordering, module_info, 
					module_info, io__state, io__state).
:- mode run_with_dependencies( in, in, out, di, uo) is det.

run_with_dependencies( Deps, HLDSin, HLDSout) -->
	list__foldl2( run_with_dependency, Deps, HLDSin, HLDSout ).

:- pred run_with_dependency( list(pred_proc_id), module_info, module_info,
				io__state, io__state).
:- mode run_with_dependency( in, in, out, di, uo ) is det.

run_with_dependency( SCC , HLDSin, HLDSout ) -->
	(
		% analysis ignores special predicates
		{ some_are_special_preds(SCC, HLDSin) }
	->
		{ HLDSout = HLDSin }
	;
		% for each list of strongly connected components, 
		% perform a fixpoint computation.
		{ sr_reuse_util__sr_fixpoint_table_init( SCC, FPtable0 ) } , 
		run_with_dependency_until_fixpoint( SCC, FPtable0, 
					HLDSin, HLDSout )
	).

:- pred some_are_special_preds( list(pred_proc_id), module_info).
:- mode some_are_special_preds( in, in ) is semidet.

some_are_special_preds( SCC, HLDS ):- 
	module_info_get_special_pred_map( HLDS, MAP), 
	map__values( MAP, SpecPRED_IDS ), 

	(
		% either some of the predicates are special 
		% preds, such as __Unify__ and others

		list__filter( pred_id_in(SpecPRED_IDS), SCC, SpecialPREDS),
		SpecialPREDS = [_|_]

	; 
		% or some of the predicates are not defined in this
		% module. 

		list__filter( not_defined_in_this_module(HLDS), SCC,
				FILTERED), 
		FILTERED = [_|_]
	).

:- pred pred_id_in( list(pred_id), pred_proc_id ).
:- mode pred_id_in( in, in) is semidet.

pred_id_in( IDS, PRED_PROC_ID):-
	PRED_PROC_ID = proc( PRED_ID, _),
	list__member( PRED_ID, IDS ). 

:- pred not_defined_in_this_module(module_info, pred_proc_id).
:- mode not_defined_in_this_module(in,in) is semidet.

not_defined_in_this_module( HLDS, proc(PREDID, _) ):-
	hlds_module__pred_not_defined_in_this_module(HLDS,
		PREDID).
	% module_info_pred_proc_info(HLDS, PRED_PROC_ID, PRED_INFO, _), 
	% pred_info_import_status(PRED_INFO, STATUS), 
	% status_defined_in_this_module(STATUS, no).

%-------------------------------------------------------------------%
:- pred run_with_dependency_until_fixpoint( list(pred_proc_id), 
		sr_reuse_util__sr_fixpoint_table, module_info, module_info,
		io__state, io__state ).
:- mode run_with_dependency_until_fixpoint( in, in, in, out, di, uo) is det.

run_with_dependency_until_fixpoint( SCC, FPtable0, HLDSin, HLDSout ) -->
	list__foldl2( analyse_pred_proc( HLDSin ), SCC, FPtable0, FPtable),
	(
		{ sr_reuse_util__sr_fixpoint_table_all_stable( FPtable) }
	->
		{ list__foldl( update_reuse_in_module_info(FPtable), SCC,
				HLDSin, HLDSout) }
	;
		{ sr_reuse_util__sr_fixpoint_table_new_run(FPtable, 
				FPtable1) },
		run_with_dependency_until_fixpoint( SCC, FPtable1, HLDSin, 
				HLDSout)
	).

:- pred analyse_pred_proc( module_info, pred_proc_id, 
				sr_fixpoint_table, sr_fixpoint_table, 
				io__state, io__state).
:- mode analyse_pred_proc( in, in, in, out, di, uo) is det.

analyse_pred_proc( HLDS, PRED_PROC_ID, FPin, FPout) --> 
	{ module_info_pred_proc_info( HLDS, PRED_PROC_ID,PredInfo,ProcInfo) },
	{ pred_info_arity(PredInfo,PredArity) },

	{ PRED_PROC_ID = proc(PredId, ProcId) },
	{ sr_reuse_util__sr_fixpoint_table_which_run(FPin, Run) },
	{ string__int_to_string( Run, SRun ) },
	{ string__append_list([ 
			"% Structure-reuse analysing (run ", SRun, ") "],
			Msg) },
	passes_aux__write_proc_progress_message( Msg, 
			PredId, ProcId, HLDS), 

	{ 
		% initialize all the necessary information to get the
		% analysis started.

		% 1. get ProcInfo
		%	OK
		% 2. get Goal
		proc_info_goal( ProcInfo, Goal0 ),
		%   	OK
		% 3. initialize alias-information
		pa_alias_as__init(Alias0),
		%	OK
		% 4. initialize reuses-information
		sr_reuse__init(PredArity, ProcInfo, Reuses0),
		% 5. analyse_goal
		analyse_goal( ProcInfo, HLDS, 
					Goal0, Goal, 
					Reuses0, Reuses,
					Alias0, _Alias, 
					FPin, FP1 ),
		% 	OK
		% 6. update all kind of information
		sr_reuse__to_tabled_reuse( Reuses, TREUSE ), 
		sr_reuse_util__sr_fixpoint_table_new_reuse( PRED_PROC_ID,
				TREUSE, Goal, FP1, FPout )
	}.
					
%-------------------------------------------------------------------%
%-- THE KERNEL STUFF
%-------------------------------------------------------------------%

:- pred analyse_goal( proc_info, module_info, 
			hlds_goal, hlds_goal,
			reuses, reuses, 
			alias_as, alias_as, 
			sr_fixpoint_table, sr_fixpoint_table).
:- mode analyse_goal( in, in, in, out, in, out, in, out, in, out ) 
			is det.
	% NOTE: the fixpoint_table can only change state wrt their
	%	stability, this is the only reason why they are threaded
	% 	through (well the first reason being to consult it).

:- pred dummy(list(hlds_goal), list(hlds_goal)).
:- mode dummy(in,out) is det.

dummy(L, L).

analyse_goal( ProcInfo, HLDS, Goal0, Goal, 
		Reuses0, Reuses, 
		Alias0, AliasRed, 
		FP0, FP ) :- 
	Goal0 = Expr0 - Info0,
	goal_info_get_nonlocals( Info0, NonLocals ), 

	% each of the branches of the following if/then/else branches
	% must instantiate:
	% 	Expr
	%	Info
	%	Reuses, 
	%	Aliases,
	% 	FP
	(
		% 1. conjunction
		Expr0 = conj(Goals0)
	->
		list_map_foldl3( analyse_goal(ProcInfo, HLDS),
				Goals0, Goals, 
				Reuses0, Reuses,
				Alias0, Alias, 
				FP0, FP),
		Info = Info0,
		Expr = conj(Goals)
	;
		% 2. call
		Expr0 = call(PredId, ProcId, ActualVars, _, _, _)
	->
		call_verify_reuse( ProcInfo, HLDS,
				PredId, ProcId, ActualVars, Alias0, 
				Reuses0, Reuses,
				Info0, Info, 
				FP0, FP),
		pa_run__extend_with_call_alias( HLDS, ProcInfo, 
	    		PredId, ProcId, ActualVars, Alias0, Alias),
		Expr = Expr0
	;
		% 3. generic_call --> see end
		% 4. switch 
		Expr0 = switch( A, B, Cases0, SM)
	->
		list_map3_foldl(
			analyse_case(ProcInfo, HLDS, 
					Reuses0, Alias0),
			Cases0, 
			Cases,
			ListReuses, 
			ListAliases,
			FP0, FP),
		sr_reuse__least_upper_bound_disjunction( NonLocals, 
					ListReuses,
					Reuses),
		pa_alias_as__least_upper_bound_list(ProcInfo, HLDS, 
					ListAliases,
					Alias),
		Info = Info0,
		Expr = switch( A, B, Cases, SM)
		
	; 
		% 5. unification
		Expr0 = unify( _, _, _, Unification, _ )
	->
		unification_verify_reuse( Unification, Alias0, 
						Reuses0, Reuses, 
						Info0, Info ),
		pa_alias_as__extend_unification( ProcInfo, HLDS, 
					Unification, Info, 
					Alias0, Alias),	
		FP = FP0,
		Expr = Expr0

	;
		% 6. disjunction	
		Expr0 = disj( Goals0, SM )
	->
		(
			Goals0 = []
		->
			Goals = Goals0, 
			Reuses = Reuses0,
			Alias = Alias0,
			FP = FP0
		;
			
			list_map3_foldl(
				pred( Gin::in, Gout::out, R::out, A::out, 
			      	FPin::in, FPout::out) is det :-
			    	(
			      	analyse_goal( ProcInfo, HLDS, 
					Gin, Gout, 
					Reuses0, R, 
					Alias0, A, 
					FPin, FPout)
			    	),
				Goals0, 
				Goals,
				ListReuses, 
				ListAliases,
				FP0, FP),
			sr_reuse__least_upper_bound_disjunction( NonLocals, 
						ListReuses,
						Reuses),
			pa_alias_as__least_upper_bound_list(ProcInfo, HLDS, 
						ListAliases,
						Alias)
		),
		Info = Info0,
		Expr = disj(Goals, SM)

	;
		% 7. not
		Expr0 = not(NegatedGoal0)
	->
		analyse_goal(ProcInfo, HLDS, 
				NegatedGoal0, NegatedGoal, 
				Reuses0, Reuses, 
				Alias0, Alias, 
				FP0, FP), 
		Info = Info0, 
		Expr = not(NegatedGoal)
	;
		% 8. some --> treated as unhandled case
		% 9. if_then_else
		Expr0 = if_then_else( Vars, Cond0, Then0, Else0, SM)
	->
		analyse_goal( ProcInfo, HLDS, Cond0, Cond, 
				Reuses0, ReusesCOND, 
				Alias0,  AliasCOND, 
				FP0, FP1),
		analyse_goal( ProcInfo, HLDS, Then0, Then, 
				ReusesCOND, ReusesTHEN, 
				AliasCOND,  AliasTHEN,
				FP1, FP2 ),
		analyse_goal( ProcInfo, HLDS, Else0, Else, 
				Reuses0, ReusesELSE, 
				Alias0,  AliasELSE,
				FP2, FP3 ), 
		sr_reuse__least_upper_bound_disjunction( NonLocals, 
					[ReusesTHEN, ReusesELSE],
					Reuses),

		pa_alias_as__least_upper_bound_list(ProcInfo, HLDS, 
					[AliasTHEN, AliasELSE],
					Alias),
		FP = FP3,
		Info = Info0,
		Expr = if_then_else( Vars, Cond, Then, Else, SM)
				
	;
		Expr = Expr0,
		Reuses = Reuses0, 
		pa_alias_as__top("unhandled goal", Alias), 
		FP = FP0,
		Info = Info0
	),
	(
		goal_is_atomic( Expr )
	->
		AliasRed = Alias % projection operation is not worthwhile
	;
		goal_info_get_outscope( Info, Outscope ),
		pa_alias_as__project_set( Outscope, Alias, AliasRed )
	),
	Goal = Expr - Info.

:- pred call_verify_reuse( proc_info, module_info, pred_id, proc_id, 
			list(prog_var), alias_as, 
			reuses, reuses, 
			hlds_goal_info , hlds_goal_info, 
			sr_fixpoint_table, sr_fixpoint_table).
:- mode call_verify_reuse( in, in, in, in, in, in, 
				in, out, 
				in, out,
				in, out) is det.

call_verify_reuse( ProcInfo, HLDS, PredId, ProcId, ActualVars, Alias0, 
					Reuses0, Reuses, 
					Info0, Info, FP0, FP ) :- 
	% 0. fetch the procinfo of the called procedure:
	module_info_pred_proc_info( HLDS, PredId, ProcId, _, 
					ProcInfo0),
	% 1. find the tabled reuse for the called predicate
	lookup_tabled_reuse( PredId, ProcId, HLDS, FP0, FP,
					FormalTREUSE),	
	% 2. once found, we can immediately handle the case where
	% the tabled reuse would say that reuse is not possible anyway:
	(
		tabled_reuse_top(FormalTREUSE)
	->
		Reuses = Reuses0,
		Info = Info0
	;
		tabled_reuse_rename( ProcInfo0, ActualVars, FormalTREUSE, 
					TREUSE ), 
		% 3. compute the Live variables upon a procedure entry:
		% 3.a. compute the full live set at the program point of
		%      the call.
		sr_live__init(LIVE0),
			% usually this should be the output variables
			% of the procedure which we're analysing, yet
			% output variables are guaranteed to belong to 
			% the LFUi set, so there is no loss in taking
			% LIVE0 as the empty live-set.
		goal_info_get_lfu(Info0, LFUi),
		goal_info_get_lbu(Info0, LBUi),
		set__union(LFUi, LBUi, LUi),
		pa_alias_as__live( LUi, LIVE0, Alias0, Live_i),
		% 3.b. project the live-set to the actual vars:
		sr_live__project( ActualVars, Live_i, ActualLive_i ),
		% 4. project the aliases to the actual vars
		pa_alias_as__project( ActualVars, Alias0, ActualAlias_i),
		(
			tabled_reuse_verify_conditions( ProcInfo, HLDS, 
				TREUSE, ActualLive_i, ActualAlias_i)
		->
			sr_reuse__add_indirect_reuse( ProcInfo, HLDS, 
				PredId, ProcId, TREUSE, LFUi, LBUi, 
				Alias0, Reuses0, Reuses),
			goal_info_set_reuse(Info0, reuse_call, Info)
		;
			Reuses = Reuses0,
			Info = Info0
		)
	).
				
			
		

			

:- pred unification_verify_reuse( hlds_goal__unification, 
			alias_as, reuses, reuses, 
			hlds_goal_info, hlds_goal_info).
:- mode unification_verify_reuse( in, in, in, out, in, out) is det.

unification_verify_reuse( Unification, Alias0, Reuses0, Reuses,
				Info0, Info) :- 
	(
		Unification = deconstruct( Var, CONS_ID, _, _, _)
	->
		goal_info_get_lfu( Info0, LFU ), 
		goal_info_get_lbu( Info0, LBU ),
		set__union( LFU, LBU, LU), 
		sr_live__init(LIVE0),
		pa_alias_as__live(LU, LIVE0, Alias0, LIVE), 
		(
			sr_live__is_live(Var,LIVE)
		->
			Info = Info0,
			Reuses = Reuses0
		;
			goal_info_set_reuse(Info0, cell_died, Info), 
			sr_reuse__add_direct_reuse( Var, CONS_ID, 
					LFU, LBU,
					Alias0, Reuses0, Reuses)
		)
	;
		Unification = construct(_, CONS_ID, _, _, _, _, _)
	->
		(
			sr_reuse__try_to_reuse( CONS_ID, Reuses0, ReuseVar, 
					ReusesTMP )
		->
			Reuses = ReusesTMP, 
			goal_info_set_reuse(Info0, cell_reused(ReuseVar), Info)
		;
			Reuses = Reuses0,
			Info = Info0
		)
	;
		% assign
		% simple_test
		% complicated_unify
		Reuses = Reuses0,
		Info = Info0
	).
				
		
:- pred analyse_case( proc_info, module_info, 
			reuses, alias_as, 
			case, case, 
			reuses,  alias_as, 
			sr_fixpoint_table, 
			sr_fixpoint_table).
:- mode analyse_case( in, in, in, in, in, out, out, out, in, out) is det.

analyse_case( ProcInfo, HLDS, Reuses0, Alias0, Case0, Case,
		Reuses, Alias, FP0, FP ):-
	Case0 = case(CONS, Goal0),
	analyse_goal( ProcInfo, HLDS, Goal0, Goal, Reuses0, Reuses, 
			Alias0, Alias, FP0, FP),
	Case = case( CONS, Goal).

:- pred list_map3_foldl( pred(T1, T2, T3, T4, T5, T5), 
			list(T1), list(T2), list(T3), list(T4),
			T5, T5).
:- mode list_map3_foldl( pred(in, out, out, out, in, out) is det,
			in, out, out, out, in, out) is det.
list_map3_foldl( P, L0, L1, L2, L3, A0, A) :- 
	(
		L0 = [ X | Xs ]
	->
		P( X, Y1, Y2, Y3, A0, A1),
		list_map3_foldl( P, Xs, Ys1, Ys2, Ys3, A1, A),
		L1 = [ Y1 | Ys1 ],
		L2 = [ Y2 | Ys2 ],
		L3 = [ Y3 | Ys3 ]
	;
		L1 = [],
		L2 = [], 
		L3 = [],
		A = A0
	).
		
:- pred list_map_foldl3( pred(T1, T2, T3, T3, T4, T4, T5, T5), 
			list(T1), list(T2),
			T3, T3, T4, T4, T5, T5).
:- mode list_map_foldl3( pred(in, out, in, out, in, out, in, out) is det,
			in, out, in, out, in, out, in, out) is det.
list_map_foldl3( P, L1, L, A1, A, B1, B, C1, C) :-
	(
		L1 = [ X | Xs ]
	->
		P( X, Y, A1, A2, B1, B2, C1, C2 ),
		list_map_foldl3( P, Xs, Ys, A2, A, B2, B, C2, C),
		L = [ Y | Ys ]
	;
		L = [],
		A = A1, 
		B = B1, 
		C = C1
	).


:- pred update_reuse_in_module_info(sr_fixpoint_table, pred_proc_id, 
				module_info, module_info).
:- mode update_reuse_in_module_info(in, in, in, out) is det.

update_reuse_in_module_info( FP, PRED_PROC_ID ,HLDSin, HLDSout) :- 
	module_info_pred_proc_info( HLDSin, PRED_PROC_ID, PredInfo0, 
					ProcInfo0),
	sr_reuse_util__sr_fixpoint_table_get_final_reuse( PRED_PROC_ID,
			TREUSE, HLDS_GOAL, FP ),
	proc_info_set_reuse_information( ProcInfo0, TREUSE, ProcInfo1 ),
	proc_info_set_goal( ProcInfo1, HLDS_GOAL, ProcInfo),
	module_info_set_pred_proc_info( HLDSin, PRED_PROC_ID, 
			PredInfo0, ProcInfo, HLDSout).

:- pred lookup_tabled_reuse( pred_id, proc_id, module_info, 
		sr_fixpoint_table, sr_fixpoint_table, 
		tabled_reuse ).
:- mode lookup_tabled_reuse( in, in, in, in, out, out) is det.

	% similar to the lookup_call_alias from pa_run:
	% 1. check in fixpoint table
	% 2. check in module_info (already fully analysed or imported pred)
	%    no special treatment necessary for primitive predicates and
	%    alike, as the default of predicates is no reuse anyway.
lookup_tabled_reuse( PredId, ProcId, HLDS, FP0, FP, TREUSE ):- 
	PRED_PROC_ID = proc(PredId, ProcId),
	(
		% 1 - check in table
		sr_reuse_util__sr_fixpoint_table_get_reuse( PRED_PROC_ID, 
					TREUSE1, FP0, FP1 )
	->
		TREUSE = TREUSE1,
		FP = FP1
	;
		FP = FP0,
		% 2 - lookup in module_info
		module_info_pred_proc_info( HLDS, PRED_PROC_ID, _PredInfo,
						ProcInfo ),
		proc_info_reuse_information( ProcInfo, TREUSE)
	).

:- pred arg_types_are_all_primitive(module_info, pred_info).
:- mode arg_types_are_all_primitive(in,in) is semidet.

arg_types_are_all_primitive(HLDS, PredInfo):-
        hlds_pred__pred_info_arg_types(PredInfo, ArgTypes),
        list__filter( pred( TYPE::in ) is semidet :-
                (
                        type_util__type_is_atomic(TYPE,HLDS)
                ),
                ArgTypes,
                _TrueList, 
                [] ).
 
