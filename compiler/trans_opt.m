%-----------------------------------------------------------------------------%
% Copyright (C) 1997-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% file: trans_opt.m
% main author: crs
%
% Transitive intermodule optimization allows the compiler to do
% intermodule optimization that depends on other .trans_opt files.  In
% comparison to .opt files, .trans_opt files allow much more accurate
% optimization to occur, but at the cost of an increased number of
% compilations required.  The fact that a .trans_opt file may depend on
% other .trans_opt files introduces the possibility of circular
% dependencies occuring. These circular dependencies would occur if the
% data in A.trans_opt depended on the data in B.trans_opt being correct,
% and vice-versa.  
%
% The following system is used to ensure that circular dependencies cannot
% occur:
% 	When mmake <module>.depend is run, mmc calculates a suitable
% 	ordering.  This ordering is then used to create each of the .d
% 	files.  This allows make to ensure that all necessary trans_opt
% 	files are up to date before creating any other trans_opt files.
% 	This same information is used by mmc to decide which trans_opt
% 	files may be imported when creating another .trans_opt file.  By
% 	observing the ordering decided upon when mmake module.depend was
% 	run, any circularities which may have been created are avoided.
%
% This module writes out the interface for transitive intermodule optimization.
% The .trans_opt file includes:
%	- pragma termination_info declarations for all exported preds
% All these items should be module qualified.
% Constructors should be explicitly type qualified.
%
% Note that the .trans_opt file does not (yet) include clauses,
% `pragma c_code' declarations, or any of the other information
% that would be needed for inlining or other optimizations;
% currently it is used *only* for termination analysis.
%
% This module also contains predicates to read in the .trans_opt files.
%
% See also intermod.m, which handles `.opt' files.
%
%-----------------------------------------------------------------------------%

:- module transform_hlds__trans_opt.

%-----------------------------------------------------------------------------%

:- interface.

:- import_module io, bool, list.
:- import_module hlds__hlds_module, parse_tree__modules, parse_tree__prog_data.

:- pred trans_opt__write_optfile(module_info, io__state, io__state).
:- mode trans_opt__write_optfile(in, di, uo) is det.

	% trans_opt__grab_optfiles(Transitive, ModuleImports0,
	% 		DontReadTheseModules, ModuleList, ModuleImports,
	% 		Error, IO0, IO).
	% Add the items from each of the modules in ModuleList.trans_opt to
	% the items in ModuleImports, do this transitively if
	% Transitive = yes.  We don't read in the list of modules in
	% DontReadTheseModules.
	%
:- pred trans_opt__grab_optfiles(bool, module_imports, list(module_name),
		list(module_name), module_imports, bool, io__state, io__state).
:- mode trans_opt__grab_optfiles(in, in, in, in, out, out, di, uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module transform_hlds__intermod, hlds__hlds_pred.
:- import_module parse_tree__mercury_to_mercury.
:- import_module parse_tree__prog_io, libs__globals, ll_backend__code_util.
:- import_module hlds__passes_aux, parse_tree__prog_out, libs__options.
:- import_module transform_hlds__termination.

:- import_module set, string, list, map, varset, term, std_util.

:- import_module pa_run.
:- import_module structure_reuse.

%-----------------------------------------------------------------------------%

% Open the file "<module-name>.trans_opt.tmp", and write out the
% declarations.

trans_opt__write_optfile(Module) -->
	{ module_info_name(Module, ModuleName) },
	module_name_to_file_name(ModuleName, ".trans_opt.tmp", yes,
					TmpOptName),
	io__open_output(TmpOptName, Result),
	(
		{ Result = error(Error) },
		{ io__error_message(Error, Msg) },
		io__progname_base("trans_opt.m", ProgName),
		io__write_string(ProgName),
		io__write_string(
			": cannot open transitive optimisation file `"),
		io__write_string(TmpOptName),
		io__write_string("' \n"),
		io__write_string(ProgName),
		io__write_string(": for output: "),
		io__write_string(Msg),
		io__nl,
		io__set_exit_status(1)
	;
		{ Result = ok(Stream) },
		io__set_output_stream(Stream, OldStream),
		{ module_info_name(Module, ModName) },
		io__write_string(":- module "),
		mercury_output_bracketed_sym_name(ModName),
		io__write_string(".\n"),

		{ module_info_get_imported_module_specifiers(Module,
				Modules0) },
		{ set__to_sorted_list(Modules0, Modules) },
		( { Modules \= [] } ->
			% XXX this could be reduced to the set that is
			% actually needed by the items being written.
			io__write_string(":- use_module "),
			io__write_list(Modules, ",",
					mercury_output_bracketed_sym_name),
			io__write_string(".\n")
		;
			[]
		),

		% All predicates to write global items into the .trans_opt 
		% file should go here.
		{ module_info_predids(Module, PredIds) },

		globals__io_lookup_bool_option(termination, Termination),
		globals__io_lookup_bool_option(infer_possible_aliases, 
							PossibleAliases),
		globals__io_lookup_bool_option(infer_structure_reuse,
							StructureReuse),

		{ module_info_structure_reuse_info(Module, StructReuseInfo) },
		{ StructReuseInfo = structure_reuse_info(ReuseMap) },
		{ map__values(ReuseMap, ReuseData) },
		{ list__map(fst, ReuseData, PredProcIds) },
		{ list__map((pred(proc(PredId, _)::in, PredId::out) is det),
				PredProcIds, StructReusePredIds) },

		{ module_info_get_special_pred_map(Module, SpecialPredMap) },
		{ map__values(SpecialPredMap, SpecialPredIds) },

		{ list__append(StructReusePredIds, SpecialPredIds,
				AllSpecialPredIds) },

		(
			{ Termination = yes }
		->
		% output termination information
		list__foldl(termination__write_pred_termination_info(Module),
			PredIds)
		;
			[]
		),
		(
			{ PossibleAliases = yes }
		->
		% output possible-alias information.
		io__write_string(
			"\n%----------- pa_alias_info/3 ------------- \n\n"),
		list__foldl(pa_run__write_pred_pa_info(Module,
							AllSpecialPredIds),
				PredIds)
		;
			[]
		),
		(
			{ StructureReuse = yes }
		->
		% output structure-reuse information
		 io__write_string(
			"\n%----------- sr_reuse_info/3 ------------- \n\n"),
		list__foldl(structure_reuse__write_pragma_reuse_info(Module, 
							AllSpecialPredIds),
				PredIds)
		;
			[]
		),
		
		io__set_output_stream(OldStream, _),
		io__close_output(Stream),

		module_name_to_file_name(ModuleName, ".trans_opt", no,
				OptName),
		update_interface(OptName),
		touch_interface_datestamp(ModuleName, ".trans_opt_date")
	).

%-----------------------------------------------------------------------------%
	% Read in and process the transitive optimization interfaces.

trans_opt__grab_optfiles(Transitive, Module0, DontReadTheseModules,
		TransOptDeps, Module, FoundError) -->
	globals__io_lookup_bool_option(verbose, Verbose),
	maybe_write_string(Verbose, "% Reading .trans_opt files..\n"),
	maybe_flush_output(Verbose),
	read_trans_opt_files(Transitive, TransOptDeps, DontReadTheseModules,
			[], OptItems, no, FoundError),

	{ append_pseudo_decl(Module0, opt_imported, Module1) },
	{ module_imports_get_items(Module1, Items0) },
	{ list__append(Items0, OptItems, Items) },
	{ module_imports_set_items(Module1, Items, Module2) },
	{ module_imports_set_error(Module2, no_module_errors, Module) },

	maybe_write_string(Verbose, "% Done.\n").

:- pred read_trans_opt_files(bool,
	list(module_name), list(module_name), item_list,
	item_list, bool, bool, io__state, io__state).
:- mode read_trans_opt_files(in, in, in, in, out, in, out, di, uo) is det.

read_trans_opt_files(_, [], _, Items, Items, Error, Error) --> [].
read_trans_opt_files(Transitive, OptFilesToRead, AlreadyReadOptFiles,
		Items0, Items, Error0, Error) -->
	{ OptFilesToRead = [Import | Imports] },
	globals__io_lookup_bool_option(very_verbose, VeryVerbose),
	maybe_write_string(VeryVerbose,
		"% Reading transitive optimization interface for module"),
	maybe_write_string(VeryVerbose, " `"),
	{ prog_out__sym_name_to_string(Import, ImportString) },
	maybe_write_string(VeryVerbose, ImportString),
	maybe_write_string(VeryVerbose, "'... "),
	maybe_flush_output(VeryVerbose),

	% XXX Nancy -- check 
	module_name_to_search_file_name(Import, ".trans_opt", FileName),
	prog_io__read_opt_file(FileName, Import, 
			ModuleError, Messages, OptItems),

	( { Transitive = yes } ->
			% Get the rest of the trans_opt files to be read.
		{ get_dependencies(OptItems, NewImportDeps0, NewUseDeps0) },
		globals__io_get_globals(Globals),
		{ get_implicit_dependencies(OptItems, Globals,
			NewImplicitImportDeps0, NewImplicitUseDeps0) },
		{ NewDeps0 = list__condense([NewImportDeps0, NewUseDeps0,
			NewImplicitImportDeps0, NewImplicitUseDeps0]) },
		{ set__list_to_set(NewDeps0, NewDepsSet0) },
		{ set__delete_list(NewDepsSet0,
			OptFilesToRead ++ AlreadyReadOptFiles, NewDepsSet) },
		{ set__to_sorted_list(NewDepsSet, NewDeps) }
	;
		{ NewDeps = [] }
	),
% 	module_name_to_search_file_name(Import, ".trans_opt", FileName),
%	prog_io__read_opt_file(FileName, Import,
%			ModuleError, Messages, Items1),

	maybe_write_string(VeryVerbose, " done.\n"),

	intermod__update_error_status(trans_opt, FileName, ModuleError,
		Messages, Error0, Error1),

	{ list__append(Items0, OptItems, Items2) },
	read_trans_opt_files(Transitive, NewDeps ++ Imports,
			[Import | AlreadyReadOptFiles],
			Items2, Items, Error1, Error).

