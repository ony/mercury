%-----------------------------------------------------------------------------%
% Copyright (C) 1996-2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_run: implements the process of annotating each procedure
%		 with possible alias information, i.e. with information
% 	 	 which states which additional parts of the 
%		 head-variables might become aliased after the procedure exits
% main author: nancy

:- module pa_run.

:- interface.

%-------------------------------------------------------------------%

:- import_module io, list.
:- import_module hlds_module, hlds_pred.
:- import_module prog_data.
:- import_module pa_alias_as.


	% the main pass
:- pred pa_run__aliases_pass( module_info, module_info, io__state, io__state).
:- mode pa_run__aliases_pass( in, out, di, uo) is det.

	% write the pa_info pragma for the given pred_id (if that
	% pred_id does not belong to the list(pred_id). 
:- pred pa_run__write_pred_pa_info( module_info, list(pred_id), pred_id, 
					io__state, io__state).
:- mode pa_run__write_pred_pa_info( in, in, in, di, uo) is det.

	% lookup the alias-information for some pred_id proc_id in the
	% module_info. Rename the alias-information to the given
	% actual parameters, and extend the given alias_as with the
	% looked up alias_as. 
	% If the given pred_id, proc_id are invalid, or no alias information
	% is found, then the operation is aborted. 
	% XXX: used by the structure reuse passes, should be moved
	% elsewhere. 
	% pa_run__extend_with_call_alias(HLDS, ProcInfo, PredId, ProcId,
	%		ActualArgs, AliasIN, AliasOUT)
	%	where 
	%		ProcInfo = proc_info of the environment in which
	%		the predicate is called
	%		PredId, ProcId = id's of the called procedure
	%		ActualArgs = args with which the proc is called
	%		AliasIN = alias at moment of call
	%		AliasOUT = alias at end of call
:- pred pa_run__extend_with_call_alias( module_info, proc_info, 
			pred_id, proc_id, 
			list(prog_var), alias_as, alias_as). 
:- mode pa_run__extend_with_call_alias( in, in, in, in, in, in, out) is det.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
:- implementation.

:- import_module require.
:- import_module list, map, int, set.
:- import_module std_util, string.

:- import_module dependency_graph.
:- import_module instmap.
:- import_module hlds_pred, hlds_goal, prog_data.
:- import_module pa_util, pa_alias_as, pa_prelim_run.
:- import_module special_pred, prog_util, prog_out.
:- import_module liveness.



%-------------------------------------------------------------------%

pa_run__aliases_pass( HLDSin, HLDSout ) -->

	% preliminary steps:
	% 1. annotate all the liveness
	{ pa_prelim_run__annotate_all_liveness_in_module( HLDSin, HLDS1 ) },

	% 2. annotate all the outscope vars
	{ pa_prelim_run__annotate_all_outscope_vars_in_module(HLDS1,HLDS2) },

	% 3. and finally do the actual aliases pass
	aliases_pass_2( HLDS2, HLDSout ).

:- pred aliases_pass_2( module_info, module_info, io__state, io__state).
:- mode aliases_pass_2( in, out, di, uo) is det.

pa_run__aliases_pass_2( HLDSin, HLDSout ) -->
		% strongly connected components needed
	{ module_info_ensure_dependency_info( HLDSin, HLDS1) },
	{ module_info_get_maybe_dependency_info( HLDS1, MaybeDepInfo) } ,
	(
		{ MaybeDepInfo = yes(DepInfo) }
	->
		{ hlds_dependency_info_get_dependency_ordering( DepInfo, DepOrdering ) },
		% perform the analysis, and annotate the procedures
		run_with_dependencies( DepOrdering, HLDS1, HLDSout) %,
		% write out the results of the exported procedures into
		% a separate interface-file. 
		% pa_run__make_pa_interface( HLDSout )
	;
		{ error("(pa) pa_run module: no dependency info") }
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
		{ pa_util__pa_fixpoint_table_init( SCC, FPtable0 ) } , 
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

:- pred run_with_dependency_until_fixpoint( list(pred_proc_id), 
		pa_util__pa_fixpoint_table, module_info, module_info,
		io__state, io__state ).
:- mode run_with_dependency_until_fixpoint( in, in, in, out, di, uo) is det.

run_with_dependency_until_fixpoint( SCC, FPtable0, HLDSin, HLDSout ) -->
	list__foldl2( analyse_pred_proc( HLDSin), SCC, FPtable0, FPtable),
	(
		{ pa_fixpoint_table_all_stable( FPtable ) }
	->
		{ list__foldl( update_alias_in_module_info(FPtable), SCC, HLDSin, HLDSout) }
	;
		{ pa_util__pa_fixpoint_table_new_run(FPtable,FPtable1) },
		run_with_dependency_until_fixpoint( SCC, FPtable1, 
				HLDSin, HLDSout )
	).

%-------------------------------------------------------------------%
% THE KERNEL 
%-------------------------------------------------------------------%
:- pred analyse_pred_proc( module_info, pred_proc_id, pa_fixpoint_table, 
				pa_fixpoint_table, io__state, io__state).
:- mode analyse_pred_proc( in, in, in, out, di, uo) is det.

analyse_pred_proc( HLDS, PRED_PROC_ID , FPtable0, FPtable) -->
	globals__io_lookup_bool_option(very_verbose,Verbose),

	{ module_info_pred_proc_info( HLDS, PRED_PROC_ID,_PredInfo,ProcInfo) },

	{ PRED_PROC_ID = proc(PredId, ProcId) },

	{ pa_util__pa_fixpoint_table_which_run(FPtable0, Run) },
	{ string__int_to_string(Run, SRun )},
	{ string__append_list( ["% Alias analysing (run ",SRun,") "],
				Msg ) },
	passes_aux__write_proc_progress_message( Msg, 
				PredId, ProcId, HLDS ), 

	{ 
		% begin non-io
	proc_info_goal( ProcInfo, Goal), 
	proc_info_headvars( ProcInfo, HeadVars),
	Goal = _ - GoalInfo,
	goal_info_get_instmap_delta(GoalInfo, InstMapDelta),
	instmap__init_reachable(InitIM),
	instmap__apply_instmap_delta(InitIM, InstMapDelta, InstMap),

	pa_alias_as__init(Alias0),
	
	analyse_goal( ProcInfo, HLDS, Goal, 
			FPtable0, FPtable1, Alias0, Alias1 ),
	% XXX
	FullSize = pa_alias_as__size( Alias1 ), 
	pa_alias_as__project( HeadVars, Alias1, Alias2),
	% XXX
	ProjectSize = pa_alias_as__size( Alias2 ),
	pa_alias_as__normalize( ProcInfo, HLDS, InstMap, Alias2, Alias ),
	% XXX
	NormSize = pa_alias_as__size( Alias ),
		
	pa_fixpoint_table_new_as( PRED_PROC_ID, Alias, FPtable1, FPtable)
	 	% end non-io 
 	}, 
	(
		{ Verbose = yes } 
	->
		%	print_maybe_possible_aliases(yes(Alias),ProcInfo), 
		%	io__write_string("\n")
		% []
		{
			string__int_to_string( FullSize, FullS ), 
			string__int_to_string( ProjectSize, ProjectS ), 
			string__int_to_string( NormSize, NormS )
		},
		io__write_strings(["\t\t: ", FullS, "/", ProjectS, "/", 
					NormS, "\n"])

	;
		[]
	).

	% analyse a given goal, with module_info and fixpoint table
	% to lookup extra information, starting from an initial abstract
	% substitution, and creating a new one. During this process,
	% the fixpoint table might change (when recursive predicates are
	% encountered).
	% analyse_goal( ProcInfo, HLDS, Goal, TableIn, TableOut,
	%		AliasIn, AliasOut ).
:- pred analyse_goal( proc_info, module_info, hlds_goal,
				pa_fixpoint_table, pa_fixpoint_table,
				alias_as, alias_as).
:- mode analyse_goal( in, in, in, in, out, in, out) is det.

analyse_goal( ProcInfo, HLDS, 
		Goal, FPtable0, FPtable, Alias0, Alias ) :- 
	Goal = GoalExpr - GoalInfo ,
	analyse_goal_expr( GoalExpr, GoalInfo, 
				ProcInfo, HLDS, 
				FPtable0, FPtable, Alias0, Alias1),
	% XXX Lets'  see what it all costs to remove them:
	(
		goal_is_atomic( GoalExpr )
	->
		Alias = Alias1	% projection operation is not worthwhile
	; 
		goal_info_get_outscope( GoalInfo, Outscope), 
		pa_alias_as__project_set( Outscope, Alias1, Alias)
	).

	
:- pred analyse_goal_expr( hlds_goal_expr, 
			   hlds_goal_info, 
				proc_info, module_info, 
				pa_fixpoint_table, pa_fixpoint_table,
				alias_as, alias_as).
:- mode analyse_goal_expr( in, in, in, in, in, out, in, out) is det.

analyse_goal_expr( conj(Goals), _Info, ProcInfo, HLDS , T0, T, A0, A) :-
	list__foldl2( analyse_goal(ProcInfo, HLDS),  Goals, 
		T0, T, A0, A).
	
	
analyse_goal_expr( call(PredID, ProcID, ARGS, _,_, _PName), _Info, 
			ProcInfo, HLDS, T0, T, A0, A):- 
	PRED_PROC_ID = proc(PredID, ProcID),
	lookup_call_alias( PRED_PROC_ID, HLDS, T0, T, CallAlias), 
	rename_call_alias( PRED_PROC_ID, HLDS, ARGS, CallAlias, RenamedCallAlias),
	pa_alias_as__extend( ProcInfo, HLDS, RenamedCallAlias, A0, A ).

analyse_goal_expr( generic_call(_,_,_,_), _Info, 
				_ProcInfo, _HLDS , T, T, _A, A):- 
	pa_alias_as__top("generic_call not handled",A).
	% error("(pa) generic_call not handled") .

analyse_goal_expr( switch(_Var,_CF,Cases,_SM), _Info, 
				ProcInfo, HLDS, T0, T, A0, A ):-
	list__map_foldl( analyse_case(ProcInfo, HLDS, A0), 
				Cases, SwitchAliases, T0, T),
	pa_alias_as__least_upper_bound_list(ProcInfo,HLDS,SwitchAliases, A ).

:- pred analyse_case( proc_info, module_info, 
			alias_as, case, alias_as, 
		   	pa_fixpoint_table,
			pa_fixpoint_table ).
:- mode analyse_case( in, in, in, in, out, in, out ) is det.

analyse_case( ProcInfo, HLDS, Alias0, CASE, Alias, T0, T ):-
	CASE = case( _, Goal),
	analyse_goal( ProcInfo, HLDS, Goal, T0, T, Alias0, Alias).

analyse_goal_expr( unify(_,_,_,Unification,_), Info, ProcInfo, HLDS, 
			T, T, A0, A ):-
	pa_alias_as__extend_unification( ProcInfo, HLDS, Unification, 
				Info, A0, A).

analyse_goal_expr( disj(Goals, _SM), _Info, ProcInfo, HLDS, T0, T, A0, A ):-
	list__map_foldl( 
		pred( Goal::in, Alias::out, FPT0::in, FPT::out) is det :- 
			( analyse_goal( ProcInfo, HLDS, Goal, 
					FPT0, FPT, A0, Alias)),
		Goals,
		DisjAliases,
		T0, T ),
	pa_alias_as__least_upper_bound_list( ProcInfo, HLDS, DisjAliases, A ).

analyse_goal_expr( not(Goal), _Info, ProcInfo, HLDS , T0, T, A0, A ):-
	analyse_goal( ProcInfo, HLDS, Goal, T0, T, A0, A).

analyse_goal_expr( some(Vars,_,Goal), _Info, ProcInfo, HLDS , T0, T, A0, A):-
	(
		Vars = []
	->
		% XXX
		analyse_goal( ProcInfo, HLDS, Goal, T0, T, A0, A)
	;
		require__error("(pa_run) analyse_goal_expr: some should have empty vars.")
	).
	% pa_alias_as__top("some not handled", A).
	% error( "(pa) some goal not handled") .

analyse_goal_expr( if_then_else(_VARS, IF, THEN, ELSE, _SM), _Info, 
			ProcInfo,
			HLDS , T0, T, A0, A) :- 
	analyse_goal( ProcInfo, HLDS, IF, T0, T1, A0, A1),
	analyse_goal( ProcInfo, HLDS, THEN, T1, T2, A1, A2),
	analyse_goal( ProcInfo, HLDS, ELSE, T2, T, A0, A3),
	pa_alias_as__least_upper_bound( ProcInfo, HLDS, A2, A3, A).

analyse_goal_expr( pragma_foreign_code( _,_,_,_, Vars, MaybeModes,Types,_  ), 
			_Info, _, HLDS , 
			T, T, Ain, A) :- 
	to_trios(Vars, MaybeModes, Types, Trios), 
	% remove all unique objects
	remove_all_unique_vars( HLDS, Trios, NonUniqueVars), 
	% keep only the output vars
	collect_all_output_vars( HLDS, NonUniqueVars, OutputVars), 
	(
		(
			OutputVars = [] 
		; 
			% XXXXXXXXXXXXXXXXX !!
			OutputVars = [_]
		)
	->
		A = Ain
	;
		list__map( 
			pred( Trio::in, Type::out ) is det:-
			( 
				Trio = trio(_, _, Type)
			), 
			OutputVars,
			OutputTypes),
		(
			types_are_primitive( HLDS, OutputTypes) 
		-> 
			A = Ain
		; 
			pa_alias_as__top("pragma_c_code not handled", A)
		)
	).

	% error( "(pa) pragma_c_code not handled") .
analyse_goal_expr( par_conj( _Goals, _SM), _Info, _, _ , T, T, _A, A) :-  
	pa_alias_as__top("par_conj not handled", A).
	% error( "(pa) par_conj not handled") .
analyse_goal_expr( bi_implication( _G1, _G2),_Info, _,  _ , T, T, _A, A) :- 
	pa_alias_as__top("bi_implication not handled", A).
	% error( "(pa) bi_implication not handled") .

%-----------------------------------------------------------------------------%



:- import_module std_util, inst_match.

:- type trio ---> trio( prog_var, mode, type). 

:- pred to_trios( list(prog_var), list(maybe(pair(string, mode))), 
			list(type), list(trio)).
:- mode to_trios( in, in, in, out) is det.

to_trios( Vars, MaybeModes, Types, Trios ):-
	(
		Vars = [ V1 | VR ]
	->
		(
			MaybeModes = [ M1 | MR ],
			Types = [ T1 | TR ]
		->
			(
				M1 = yes( _String - Mode )
			->
				Trio1 = trio( V1, Mode, T1), 
				to_trios( VR, MR, TR, TrioR), 
				Trios = [ Trio1 | TrioR ]
			;
				to_trios( VR, MR, TR, Trios )
			)
		;
			require__error("(pa_run) to_trios: lists of different length.")
		)
	;
		(
			MaybeModes = [], Types = []
		->
			Trios = []
		;
			require__error("(pa_run) to_trios: not all lists empty.")
		)
	).
			
:- pred collect_all_output_vars( module_info::in, 
		list(trio)::in, list(trio)::out) is det.
:- pred remove_all_unique_vars( module_info::in, 
		list(trio)::in, list(trio)::out) is det.
:- pred collect_all_input_vars( module_info::in,
		list(trio)::in, list(trio)::out) is det.

:- import_module mode_util.

collect_all_output_vars( HLDS, VarsIN, VarsOUT):- 
	list__filter(
		pred( P0::in ) is semidet :- 
		(
			P0 = trio(_, Mode, Type), 
			mode_to_arg_mode(HLDS, Mode, Type, ArgMode), 
			ArgMode = top_out
		), 
		VarsIN, 
		VarsOUT
	).
	
remove_all_unique_vars( HLDS, VarsIN, VarsOUT):- 
	list__filter(
		pred( P0::in ) is semidet :- 
		(
			P0 = trio(_, Mode, _), 
			Mode = (_LeftInst -> RightInst), 
			\+ inst_is_unique(HLDS, RightInst), 
			\+ inst_is_clobbered(HLDS, RightInst)
		),
		VarsIN, 
		VarsOUT
	).

collect_all_input_vars( HLDS, VarsIN, VarsOUT):- 
	list__filter(
		pred( P0::in ) is semidet :- 
		(
			P0 = trio(_, Mode, Type), 
			mode_to_arg_mode(HLDS, Mode, Type, ArgMode), 
			ArgMode = top_in
		), 
		VarsIN, 
		VarsOUT
	).

%-----------------------------------------------------------------------------%

	% lookup the alias of the procedure with given pred_proc_id and
	% find it's output abstract substitution. 
	% 1 - look first in table, if this fails (then not in same SCC)
	% 2 - look in module_info (as we might already have analysed the 
	%     predicate, if defined in same module, or analysed in other 
	%     imported module)
	% 3 - check whether the args have primitive types -- then no aliases
	%     can be created by the call
	% 4 - react appropriately if the calls happen to be to 
	%     * either compiler generated predicates
	%     * or predicates from builtin.m and private_builtin.m
:- pred lookup_call_alias( pred_proc_id, module_info, pa_fixpoint_table,
				pa_fixpoint_table, alias_as ).
:- mode lookup_call_alias( in, in, in, out, out) is det.

lookup_call_alias( PRED_PROC_ID, HLDS, FPtable0, FPtable, Alias) :-
	(
		% 1 - check in table
		pa_fixpoint_table_get_as( PRED_PROC_ID, Alias1, 
					FPtable0, FPtable1)
	->
		FPtable = FPtable1,
		Alias   = Alias1
	;
		% 2 - look up in module_info
		lookup_call_alias_in_module_info( HLDS, PRED_PROC_ID, 
				Alias), 
		FPtable = FPtable0
	).

	% exported predicate
extend_with_call_alias( HLDS, ProcInfo, 
		PRED_ID, PROC_ID, ARGS, ALIASin, ALIASout ):-
	PRED_PROC_ID = proc(PRED_ID, PROC_ID), 
	lookup_call_alias_in_module_info( HLDS, PRED_PROC_ID, ALIAS_tmp), 
	rename_call_alias( PRED_PROC_ID, HLDS, ARGS, ALIAS_tmp, ALIAS_call),
	pa_alias_as__extend( ProcInfo, HLDS, ALIAS_call, ALIASin, ALIASout). 
	
:- pred lookup_call_alias_in_module_info( module_info, pred_proc_id, 
		alias_as). 
:- mode lookup_call_alias_in_module_info( in, in, out) is det.

lookup_call_alias_in_module_info( HLDS, PRED_PROC_ID, Alias) :- 
	module_info_pred_proc_info( HLDS, PRED_PROC_ID, PredInfo,
				    ProcInfo),
	(
		proc_info_possible_aliases(ProcInfo, MaybeAliases),
		MaybeAliases = yes( SomeAL)
	->
		Alias = SomeAL
	;
		% check whether the args are primitive types
		arg_types_are_all_primitive(HLDS, PredInfo)
	->
		init(Alias)
	;
		% 4 - call to builtin.m or private_builtin.m
		%     predicate -- unify/index/compare
		pred_info_name(PredInfo, Name),
		pred_info_arity(PredInfo, Arity),
		(
			special_pred_name_arity(_, Name, _, Arity),
			pred_info_module(PredInfo, ModuleName),
			( 
				mercury_private_builtin_module(ModuleName)
			; 
				mercury_public_builtin_module(ModuleName)
			)
		;
			special_pred_name_arity(_, _, Name, Arity)
		)
	->
		% no aliases created
		init(Alias)
	;
		% XXX Any call to private_builtin.m module!
		pred_info_module(PredInfo, ModuleName),
		mercury_private_builtin_module(ModuleName)
	->
		% no aliases created
		init(Alias)
	;
		% if all else fails --> ERROR !! 
		
		PRED_PROC_ID = proc(PRED_ID, PROC_ID),
		pred_info_name(PredInfo, PNAME), 
		pred_info_module(PredInfo, PMODULE),
		prog_out__sym_name_to_string(PMODULE, SPMODULE),	
		pred_info_import_status(PredInfo, Status),
		import_status_to_minimal_string(Status, SStatus),
		pred_id_to_int(PRED_ID, IPRED_ID),
		proc_id_to_int(PROC_ID, IPROC_ID),
		string__int_to_string(IPRED_ID, SPRED_ID),
		string__int_to_string(IPROC_ID, SPROC_ID),
		string__append_list(["lookup alias failed for ", 
			SPMODULE, "::",
			PNAME,"(",SPRED_ID, ",", SPROC_ID, ",",
				SStatus, ")"], 
			ErrMsg), 
		top(ErrMsg, Alias)
	).

:- import_module type_util.

:- pred arg_types_are_all_primitive(module_info, pred_info).
:- mode arg_types_are_all_primitive(in,in) is semidet.

arg_types_are_all_primitive(HLDS, PredInfo):-
	hlds_pred__pred_info_arg_types(PredInfo, ArgTypes),
	types_are_primitive( HLDS, ArgTypes).

:- pred types_are_primitive( module_info::in, list(type)::in) is semidet.

types_are_primitive( HLDS, TYPES ) :- 
	list__filter( pred( TYPE::in ) is semidet :-
		(
			type_util__type_is_atomic(TYPE,HLDS)
		),
		TYPES,
		_TrueList, 
		[] ).




:- pred rename_call_alias( pred_proc_id, module_info, list(prog_var),
				alias_as, alias_as).
:- mode rename_call_alias( in, in, in, in, out) is det.

rename_call_alias( PRED_PROC_ID, HLDS, ARGS, Ain, Aout ):-
	module_info_pred_proc_info( HLDS, PRED_PROC_ID, _P, ProcInfo),
	proc_info_headvars(ProcInfo, Headvars),
	map__from_corresponding_lists(Headvars,ARGS,Dict),
	pa_alias_as__rename( Dict, Ain, Aout ).

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
% easy stuff

	% once the abstract alias substitution is computed for
	% a procedure, one must simply update the proc-information
	% of that procedure.
:- pred update_alias_in_module_info(pa_util__pa_fixpoint_table, 
					pred_proc_id, module_info,
					module_info).
:- mode update_alias_in_module_info(in, in, in, out) is det.

update_alias_in_module_info( FPtable, PRED_PROC_ID, HLDSin, HLDSout) :-
	module_info_pred_proc_info(HLDSin, PRED_PROC_ID, PredInfo, ProcInfo),
	pa_fixpoint_table_get_final_as( PRED_PROC_ID, ALIAS_AS, FPtable),
	proc_info_set_possible_aliases( ProcInfo, ALIAS_AS, NewProcInfo),
	module_info_set_pred_proc_info(HLDSin, PRED_PROC_ID, PredInfo,
					NewProcInfo, HLDSout).


%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
% make the interface

:- import_module globals, modules, passes_aux, bool, options.
:- import_module varset.
:- import_module mercury_to_mercury.

	% inspiration taken from termination.m
:- pred pa_run__make_pa_interface( module_info, io__state, io__state ).
:- mode pa_run__make_pa_interface( in, di, uo ) is det.

pa_run__make_pa_interface( HLDS ) --> 
	{ module_info_name( HLDS, ModuleName ) },
	modules__module_name_to_file_name( ModuleName, ".opt.pa", bool__no, KaFileName),
	globals__io_lookup_bool_option(verbose, Verbose),
	maybe_write_string(Verbose, "% -> writing possible aliases to `"),
	maybe_write_string(Verbose, KaFileName ),
	maybe_write_string(Verbose, "'..."),
	maybe_flush_output(Verbose),

	io__open_output( KaFileName, KaFileRes ),
	(
		{ KaFileRes = ok(KaFile) },
		io__set_output_stream( KaFile, OldStream ),
		pa_run__make_pa_interface_2( HLDS ), 
		io__set_output_stream( OldStream, _ ),
		io__close_output( KaFile ),
		maybe_write_string(Verbose, " done.\n"),
		maybe_flush_output(Verbose)
	;
		{ KaFileRes = error( IOError ) },
		maybe_write_string(Verbose, " failed!\n"),
		maybe_flush_output(Verbose),
		{ io__error_message( IOError, IOErrorMsg ) },
		io__write_strings(["Error opening file `",
                        KaFileName, "' for output: ", IOErrorMsg]),
		io__set_exit_status(1)
        ).

:- pred pa_run__make_pa_interface_2( module_info, 
					io__state, io__state).
:- mode pa_run__make_pa_interface_2( in, di, uo) is det.

pa_run__make_pa_interface_2( HLDS ) -->
	{ module_info_name( HLDS, ModuleName ) },
	{ module_info_predids( HLDS, PredIds ) },
	{ module_info_get_special_pred_map( HLDS, MAP ) },
	{ map__values( MAP, SpecPredIds ) },
	io__write_string(":- module "),
	mercury_output_sym_name( ModuleName ), 
	io__write_string(".\n\n"),
	io__write_string(":- interface. \n"),
	list__foldl( make_pa_interface_pred(HLDS, SpecPredIds), PredIds ).

pa_run__write_pred_pa_info( HLDS, SpecPredIds, PredId) -->
	pa_run__make_pa_interface_pred( HLDS, SpecPredIds, PredId).

:- pred pa_run__make_pa_interface_pred(module_info, list(pred_id),pred_id, 
					io__state, io__state).
:- mode pa_run__make_pa_interface_pred( in, in, in, di ,uo) is det.

pa_run__make_pa_interface_pred( HLDS, SpecPredIds, PredId ) -->
	{ module_info_pred_info( HLDS, PredId, PredInfo ) },
	(
		{ pred_info_is_exported( PredInfo ) }
	->
		( 
			{ list__member( PredId, SpecPredIds ) }
		->
			[]
		;
			{ pred_info_procids(PredInfo, ProcIds) },
			{ pred_info_procedures( PredInfo, ProcTable ) },
			list__foldl( make_pa_interface_pred_proc( PredInfo, ProcTable),
					ProcIds )
		)
	;
		[]
	).

:- pred pa_run__make_pa_interface_pred_proc( pred_info, proc_table, proc_id,
						io__state, io__state).
:- mode pa_run__make_pa_interface_pred_proc( in, in, in, di, uo) is det.

pa_run__make_pa_interface_pred_proc( PredInfo, ProcTable, ProcId) -->
	io__write_string(":- pragma pa_alias_info("),

		% write a simple predicate declaration

	{ varset__init( InitVarSet ) },
	{ pred_info_name( PredInfo, PredName ) },
	{ pred_info_get_is_pred_or_func( PredInfo, PredOrFunc ) },
	{ pred_info_module( PredInfo, ModuleName ) },
	{ pred_info_context( PredInfo, Context ) },
	{ pred_info_arity( PredInfo, Arity) },
	{ SymName = qualified( ModuleName, PredName ) },

	{ map__lookup( ProcTable, ProcId, ProcInfo ) },
	{ proc_info_declared_argmodes( ProcInfo, Modes ) },

	(
		{ PredOrFunc = predicate },
		mercury_output_pred_mode_subdecl( InitVarSet, SymName, Modes,
			std_util__no, Context )
	;
		{ PredOrFunc = function },
		{ pred_args_to_func_args( Modes, FuncModes, RetMode ) },
		mercury_output_func_mode_subdecl( InitVarSet, SymName, 
			FuncModes, RetMode, std_util__no, Context )
	),

	io__write_string(", "),

		% write headvars vars(HeadVar__1, ... HeadVar__n)

	{ proc_info_varset(ProcInfo, ProgVarset) },
	{ proc_info_headvars(ProcInfo, HeadVars) },
	{ list__length(HeadVars, PseudoArity) }, 
	{ NumberOfTypeInfos = PseudoArity - Arity },
	{ list_drop_det(NumberOfTypeInfos, HeadVars, RealHeadVars) },
	io__write_string("vars("),
	mercury_output_vars(RealHeadVars, ProgVarset, no),
	io__write_string(")"),

	io__write_string(", "),

		% write alias information

	{ proc_info_possible_aliases(ProcInfo, MaybeAliases) },

	pa_alias_as__print_maybe_interface_aliases( MaybeAliases, ProcInfo),

	io__write_string(").\n").

	% list_drop_det(Len,List,End):
	% 	deterministic version of list__drop.
	%	If `List' has less than `Len' elements, return the 
	% 	entire list.

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

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
% ensure loaded interfaces.

/*********************************************************************
:- import_module term, set, prog_io, globals, prog_out, prog_io_util.
:- import_module hlds_out, assoc_list, mode_util.

	% load interfaces of the imported modules. 
	% If some interface file appears to be unavailable, a warning
	% is generated, and probably the code will fail at some later
	% point. 
:- pred pa_run__ensure_loaded_interfaces( module_info, module_info, 
						io__state, io__state).
:- mode pa_run__ensure_loaded_interfaces( in, out, di, uo) is det.

pa_run__ensure_loaded_interfaces( HLDS0, HLDS) -->
	{ module_info_get_imported_module_specifiers( HLDS0, ModSpecs ) },
	{ set__to_sorted_list( ModSpecs, LModSpecs ) },
	list__foldl2( load_interface, LModSpecs, HLDS0, HLDS).

:- pred load_interface( module_specifier, module_info, module_info,
			io__state, io__state).
:- mode load_interface( in, in, out, di, uo) is det.

load_interface( ModuleSpec, HLDS0, HLDS ) -->
	globals__io_lookup_bool_option(very_verbose, VeryVerbose),
	module_name_to_file_name( ModuleSpec, ".opt.pa", no, FileName ),
	maybe_write_string(VeryVerbose, "% Reading `"),
	maybe_write_string(VeryVerbose, FileName ),
	maybe_write_string(VeryVerbose, "'... "),
	maybe_flush_output(VeryVerbose),
	prog_io__read_module( FileName, ModuleSpec, yes, Err, _ModuleName, 
				Msgs, Items),
	(
		{ Err = fatal }
	->
		maybe_write_string(VeryVerbose, "fatal error(s).\n")
	;
		{ Err = yes }
	->
		maybe_write_string(VeryVerbose, "parse_error(s).\n")
	;
		maybe_write_string(VeryVerbose, "successfull parse.\n")
	),
	prog_out__write_messages(Msgs),
	(
		{ Err = fatal }
	-> 
		maybe_write_string(VeryVerbose, "% Continuing... errors might occur later.\n")
	;
		{ Err = yes }
	->
		maybe_write_string(VeryVerbose, "% Continuing... errors might occur later.\n")
	;
		maybe_write_string(VeryVerbose, "% Cool!\n")
	),

	list__foldl2( add_item_from_opt_pa, Items, HLDS0, HLDS ).

:- pred add_item_from_opt_pa( item_and_context, module_info, module_info, 
					io__state, io__state ).
:- mode add_item_from_opt_pa( in, in, out, di, uo) is det.

add_item_from_opt_pa( Item - _Context, HLDS0, HLDS ) -->
	(
		{ Item = pragma(Pragma) }
	->
		add_pragma_item_from_opt_pa( Pragma , HLDS0, HLDS)
	;
	 	prog_io_util__report_warning(
				"Only pragma pa_alias_info allowed in `.opt.pa' file.")	,
		{ HLDS = HLDS0 }
	).

:- pred add_pragma_item_from_opt_pa( pragma_type, module_info, module_info,
					io__state, io__state).
:- mode add_pragma_item_from_opt_pa( in, in, out, di, uo) is det.

add_pragma_item_from_opt_pa( Pragma, HLDS0, HLDS) -->
	(
		{ Pragma = pa_alias_info( PredOrFunc, SymName, Modes,
					HeadVars, MaybeAlias) }
	->
		add_pragma_possible_aliases_info( PredOrFunc, SymName, Modes,
					HeadVars, MaybeAlias, HLDS0, HLDS)
	;
		prog_io_util__report_warning(
				"Only pragma pa_alias_info allowed in `.opt.pa' file.")	,
		{ HLDS = HLDS0 }
	).

*************************************************************************/


