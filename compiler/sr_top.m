%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_top
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
% 			% aliasing of H1 is true.  A deconstruction
% 			% generating a dead cell, followed by a
% 			% construction reusing that cell, is called a direct
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

:- module structure_reuse__sr_top.
:- interface.

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module possible_alias__pa_alias_as.

:- import_module list, io, bool, std_util.

	% Perform the structure reuse analysis. 
:- pred structure_reuse(module_info::in, maybe(alias_as_table)::in, 
		bool::in, bool::in, module_info::out, 
		io__state::di, io__state::uo) is det.

	% Write the reuse information of a module as pragma's in the trans_opt
	% of that module. 
	% XXX This procedure should be defined elsewhere. 
:- pred write_pragma_reuse_info(module_info::in, list(pred_id)::in,
	pred_id::in, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_out.
:- import_module hlds__passes_aux.
:- import_module libs__globals.
:- import_module libs__options.
:- import_module parse_tree__mercury_to_mercury.
:- import_module parse_tree__prog_data.
:- import_module possible_alias__pa_sr_util.	
:- import_module structure_reuse__sr_data.
:- import_module structure_reuse__sr_direct.
:- import_module structure_reuse__sr_indirect.
:- import_module structure_reuse__sr_profile_run.
:- import_module structure_reuse__sr_split.
:- import_module structure_reuse__sr_split.

:- import_module list, map, varset, std_util, int, bool.
:- import_module term, require.

structure_reuse(HLDS0, MaybeAliasTable, Verbose, Stats, HLDS) -->
	globals__io_lookup_bool_option(infer_structure_reuse, Reuse),
	( 	
		{ Reuse = yes }
	->
		(
			{ MaybeAliasTable = yes(AliasTable) }
		->
			maybe_write_string(Verbose, 
					"% Structure-reuse analysis...\n"),
			maybe_flush_output(Verbose),
			structure_reuse(AliasTable, HLDS0, HLDS),
			maybe_write_string(Verbose, "% done.\n"),
			maybe_report_stats(Stats)
		;
			{ Msg = "(sr_top) No aliastable." },
			{ error(Msg) }
		)
	;
		{ HLDS = HLDS0 }
	).

:- pred structure_reuse(alias_as_table::in, 
		module_info::in, module_info::out,
		io::di, io::uo) is det.

structure_reuse(AliasTable, HLDS00, HLDS) -->
	% Before starting the actual reuse-analysis, process all the reuse
	% information of the imported predicates.
	{ module_info_unproc_reuse_pragmas(HLDS00, UnprocReusePragmas) },
	list__foldl2(
		process_unproc_reuse_pragma, UnprocReusePragmas, 
		HLDS00, HLDS01), 
	{ module_info_remove_unproc_reuse_pragmas(HLDS01, HLDS0) }, 

	% We do not want to analyse predicates that are introduced by the
	% compiler. We will therefore filter out these predicates.
	{ module_info_get_special_pred_map(HLDS0, SpecialPredMap) },
	{ map__values(SpecialPredMap, SpecialPredIds) },

		% Do the direct reuse analysis phase.
	process_matching_nonimported_procs(
			update_module_io(sr_direct__process_proc(AliasTable)),
			(pred(PredId::in, _PredInfo::in) is semidet :-
				\+ list__member(PredId, SpecialPredIds)
			),
			HLDS0, HLDS1),

		% Do the fixpoint computation to determine all the indirect
		% reuse, and the implied conditions.
	sr_indirect__compute_fixpoint(AliasTable, HLDS1, HLDS2),
	sr_split__create_multiple_versions(HLDS2, HLDS), 
	sr_profile_run__structure_reuse_profiling(HLDS). 

%-----------------------------------------------------------------------------%
:- pred process_unproc_reuse_pragma(unproc_reuse_pragma, module_info, 
		module_info, io__state, io__state).
:- mode process_unproc_reuse_pragma(in, in, out, di, uo) is det.

process_unproc_reuse_pragma(UnprocReusePragma, Module0, Module) --> 
	{ UnprocReusePragma = unproc_reuse_pragma(PredOrFunc, SymName, 
		Modes, HeadVars, Types, Reuse, _MaybeReuseName) },

	globals__io_lookup_bool_option(very_verbose, VeryVerbose),

	{ module_info_get_predicate_table(Module0, Preds) }, 
	{ module_info_preds(Module0, PredTable0) },
	{ list__length(Modes, Arity) },
	( 
		{ predicate_table_search_pf_sym_arity_declmodes(
				Module0, Preds, PredOrFunc, SymName, 
				Arity, Modes, PredId, ProcId) }
	->
		{ map__lookup(PredTable0, PredId, PredInfo0) },
		{ pred_info_procedures(PredInfo0, ProcTable0) },
		{ map__lookup(ProcTable0, ProcId, ProcInfo0) },

		write_proc_progress_message("(Reuse) Looking into ", 
			PredId, ProcId, Module0),

			% rename the headvars: 
		maybe_write_string(VeryVerbose, "Renaming HeadVars/Types..."),
		{ proc_info_headvars(ProcInfo0, ProcHeadVars) }, 
		{ list__map(term__coerce_var, HeadVars, CHVars) },
		{ map__from_corresponding_lists(CHVars, ProcHeadVars,
			MapHeadVars) }, 
		{ pred_info_arg_types(PredInfo0, ArgTypes) },
		{ sr_data__memo_reuse_rename(MapHeadVars, 
			yes(to_type_renaming(Types, ArgTypes)), 
			Reuse, Reuse2) },
		maybe_write_string(VeryVerbose, "done.\n"),

		% create the reuse-version of the procedure
		{ sr_split__create_reuse_pred(proc(PredId, ProcId),
			Reuse2, no, Module0, Module) }
		
	;
		% XXX Currently a lot of pragma's with no corresponding
		% procedure in the predicate table are read. Yet a priori
		% this is without consequences for the analysis. Either this 
		% should be studied more closely, or correct warnings should
		% be produced. 
		% io__write_string("Warning: no entry found for "),
		% hlds_out__write_simple_call_id(PredOrFunc, SymName/Arity),
		% io__write_string(" with modes: "), 
		% { varset__init(EmptyVarset) },
		% io__write_list(Modes, ", ", write_mode(EmptyVarset)),
		% io__write_string(" (reuse_info).\n"),
		{ Module = Module0 }
	).

% :- import_module mercury_to_mercury.
% :- pred write_mode(varset, (mode), io__state, io__state).
% :- mode write_mode(in, in, di, uo) is det.
% write_mode(Varset, Mode) --> 
	% { varset__coerce(Varset, CVarset) },
	% io__write_string(mercury_mode_to_string(Mode, CVarset)).

%-----------------------------------------------------------------------------%


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

:- pred write_pred_proc_sr_reuse_info( module_info, pred_id,
                                proc_id, io__state, io__state).
:- mode write_pred_proc_sr_reuse_info( in, in, in, di, uo) is det.

write_pred_proc_sr_reuse_info( HLDS, PredId, ProcId) -->
	{ module_info_pred_proc_info(HLDS, PredId, ProcId,
			PredInfo, ProcInfo) },

	io__write_string(":- pragma structure_reuse("),

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
	{ proc_info_headvars(ProcInfo, HeadVars) },
	{ proc_info_vartypes(ProcInfo, VarTypes) }, 
	{ pred_info_typevarset(PredInfo, TypeVarSet) },

	pa_sr_util__trans_opt_output_vars_and_types(
			ProgVarset, 
			VarTypes, 
			TypeVarSet, 
			HeadVars),

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
	sr_data__memo_reuse_print(TREUSE, ReuseName, ReuseProcInfo, PredInfo) ,

	io__write_string(").\n").
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
