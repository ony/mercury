%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	structure_reuse
% Main authors: nancy, petdr
%
% The top level module for placing structure reuse annotations onto the
% HLDS.
%
% Structure reuse is broken up into two phases: the direct reuse
% analysis (sr_direct) and the indirect analysis (sr_indirect).
% 
% list__append(H1, H2, H3) :-
% 	(
% 		H1 => [],
% 		H3 := H2
% 	;
% 			% Cell H1 dies provided some condition about the
% 			% aliasing of H1 is true.  This is a direct
% 			% reuse.
% 		H1 => [X | Xs],
%
% 			% If the condition about the aliasing of H1
% 			% is true then we can call the version of
% 			% list__append which does reuse.
% 			% This is an indirect reuse.
% 		list__append(Xs, H2, Zs),
%
%			% Reuse the dead cell H1.  This is a direct
%			% reuse.
% 		H3 <= [X | Zs]
% 	).
%
%-----------------------------------------------------------------------------%

:- module structure_reuse.
:- interface.

:- import_module list,io.
:- import_module hlds_module, hlds_pred.

:- pred structure_reuse(module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.
:- pred write_pragma_reuse_info(module_info::in, list(pred_id)::in,
		pred_id::in, io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module passes_aux, sr_direct, sr_indirect, sr_split, sr_util.
:- import_module list, map, varset, std_util, int, bool.
:- import_module sr_profile_run.

structure_reuse(HLDS0, HLDS) -->
	{ module_info_get_special_pred_map(HLDS0, SpecialPredMap) },
	{ map__values(SpecialPredMap, SpecialPredIds) },

		% Do the direct reuse analysis phase.
	process_matching_nonimported_procs(
			update_module_io(sr_direct__process_proc),
			(pred(PredId::in, _PredInfo::in) is semidet :-
				\+ list__member(PredId, SpecialPredIds)
			),
			HLDS0, HLDS1),

		% Do the fixpoint computation to determine all the indirect
		% reuse, and the implied conditions.
	sr_indirect__compute_fixpoint(HLDS1, HLDS2),
	sr_split__create_multiple_versions(HLDS0, HLDS2, HLDS), 
	sr_profile_run__structure_reuse_profiling(HLDS). 


write_pragma_reuse_info( HLDS, SpecPredIds, PredId ) --> 
	{ module_info_pred_info( HLDS, PredId, PredInfo ) },
	(
		{ pred_info_is_exported( PredInfo ) ; 
		  pred_info_is_opt_exported( PredInfo) }
	
	->
		( 
			{ list__member( PredId, SpecPredIds ) }
		->
			[]
		;
			{ pred_info_procids(PredInfo, ProcIds) },
			list__foldl( 
				write_pred_proc_sr_reuse_info(HLDS, PredId),
					ProcIds )
		)
	;
		[]
	).

:- import_module sr_data.	
:- import_module mercury_to_mercury, prog_data.

:- pred write_pred_proc_sr_reuse_info( module_info, pred_id,
                                proc_id, io__state, io__state).
:- mode write_pred_proc_sr_reuse_info( in, in, in, di, uo) is det.

write_pred_proc_sr_reuse_info( HLDS, PredId, ProcId) -->
	{ module_info_pred_proc_info(HLDS, PredId, ProcId,
			PredInfo, ProcInfo) },

	io__write_string(":- pragma sr_reuse_info("),

		% write a simple predicate declaration

	{ varset__init( InitVarSet ) },
	{ pred_info_name( PredInfo, PredName ) },
	{ pred_info_get_is_pred_or_func( PredInfo, PredOrFunc ) },
	{ pred_info_module( PredInfo, ModuleName ) },
	{ pred_info_context( PredInfo, Context ) },
	{ SymName = qualified( ModuleName, PredName ) },

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
	{ proc_info_real_headvars(ProcInfo, HeadVars) },

	{ RealHeadVars = HeadVars }, 

	( { RealHeadVars = [] } ->
		io__write_string("vars")
	;
		io__write_string("vars("),
		mercury_output_vars(RealHeadVars, ProgVarset, no),
		io__write_string(")")
	),
	io__write_string(", "),

		% write reuse information
	{ module_info_structure_reuse_info(HLDS, ReuseInfo) },
	{ ReuseInfo = structure_reuse_info(ReuseMap) },
	{ 
		map__search(ReuseMap, proc(PredId, ProcId), Result)
	->
		Result = proc(ReusePredId, ReuseProcId) - ReuseName
	;
		ReusePredId = PredId,
		ReuseProcId = ProcId,
		ReuseName = SymName
	},
	{ module_info_pred_proc_info(HLDS, ReusePredId, ReuseProcId,
			_ReusePredInfo, ReuseProcInfo) },
	{ proc_info_reuse_information(ReuseProcInfo, TREUSE) },
	sr_data__memo_reuse_print( TREUSE, ReuseName, ReuseProcInfo) ,

	io__write_string(").\n").
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
