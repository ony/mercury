%-----------------------------------------------------------------------------%
% Copyright (C) 1997 University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% file: trans_opt.m
% main author: crs
%
% Transitive intermodule optimization allows the compiler to do
% intermodule optimization that depends on other .trans_opt files.  This
% allows much more accurate optimization to occur, but at the cost of an
% increased number of compilations required.  The fact that a .trans_opt
% file may depend on other .trans_opt files has a possibility of circular
% dependencies occuring. These circular dependencies would occur if the
% data in A.trans_opt depended on the data in B.trans_opt being correct,
% and vice-versa.  To prevent this occuring, when mmake <module>.depend is
% run, it outputs a .order file. This file contains a list of all the
% modules in the current program, sorted topologically.  As a result, any
% module may import a .trans_opt file from another module if and only if
% that other module appears after the current module in the .order file.
% The reason that more compilations are required for .trans_opt files than
% for .opt files is that each .trans_opt file depends not only on the
% current .m file, but also on each .trans_opt file corresponding to each
% module that is both below the current module in the .order file, and is
% imported by the current module.  This increased number of dependencies
% results in an increased number of recompilations.
%
% This module writes out the interface for transitive intermodule optimization.
% The .trans_opt file includes:
%	- pragma opt_terminates declarations for all exported preds
% All these items should be module qualified.
% Constructors should be explicitly type qualified.
%
% This module also contains predicates to read in the .trans_opt files.
% 
% Transitive intermodule optimization is currently a work in progress.
% The current implementation correctly outputs the trans_opt file when the
% --make-trans-opt option is given, and also correctly imports other
% trans_opt files.  What is not finished is as follows:
%
% -	The name of the .order file is not yet finalised and the references
% 	to it in this document may need to be changed
% -	The compiler currently imports the .trans_opt files of all the modules
% 	that are imported.  It should only import the .trans_opt files that
% 	are below it in the .order file
% -	There is no documentation highlighting the fact that transitive
%	optimization depends on 'mmake depend' 
% 
%-----------------------------------------------------------------------------%

:- module trans_opt.

%-----------------------------------------------------------------------------%

:- interface.

:- import_module io, bool, hlds_module, modules.

:- pred trans_opt__write_optfile(module_info, io__state, io__state).
:- mode trans_opt__write_optfile(in, di, uo) is det.

	% Add the items from the .trans_opt files of imported modules to
	% the items for this module.
:- pred trans_opt__grab_optfiles(module_imports, module_imports, bool,
				io__state, io__state).
:- mode trans_opt__grab_optfiles(in, out, out, di, uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module hlds_pred, mercury_to_mercury, varset, term, std_util.
:- import_module prog_io, string, list, map, globals, code_util.
:- import_module passes_aux, prog_data, prog_out, options, termination.

%-----------------------------------------------------------------------------%

% Open the file "<module-name>.trans_opt", and write out the
% declarations.

trans_opt__write_optfile(Module) -->
	{ module_info_name(Module, ModuleName) },
	% XXX this should be .trans_opt.tmp, and it should be compared
	% at the end of making the .trans_opt.tmp 
	{ string__append(ModuleName, ".trans_opt", OptName) },
	io__open_output(OptName, Result),
	(
		{ Result = error(Error) },
		{ io__error_message(Error, Msg) },
		io__progname_base("termination.m", ProgName),
		io__write_string(ProgName),
		io__write_string(
			": cannot open transitive optimisation file '"),
		io__write_string(OptName),
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
		mercury_output_bracketed_constant(term__atom(ModName)),
		io__write_string(".\n"),

		% all predicates to write global items into the .trans_opt 
		% file should go here.

		{ module_info_predids(Module, PredIds) },
		trans_opt__write_preds(PredIds, Module),

		io__set_output_stream(OldStream, _),
		io__close_output(Stream)
	).
	
:- pred trans_opt__write_preds(list(pred_id), module_info, 
	io__state, io__state).
:- mode trans_opt__write_preds(in, in, di, uo) is det.
trans_opt__write_preds([], _) --> [].
trans_opt__write_preds([ PredId | PredIds ], Module) -->
	{ module_info_preds(Module, PredTable) },
	{ map__lookup(PredTable, PredId, PredInfo) },

	( 	
		{ pred_info_is_exported(PredInfo) },
		\+ { code_util__predinfo_is_builtin(PredInfo) },
		\+ { code_util__compiler_generated(PredInfo) }
	->
		% all predicates to write predicate info into the .trans_opt 
		% file should go here.
		{ pred_info_procedures(PredInfo, ProcTable) },
		{ map__keys(ProcTable, ProcIds) },
		trans_opt__write_procs(ProcIds, PredId, PredInfo)
	;
		[]
	),
	trans_opt__write_preds(PredIds, Module).
	
:- pred trans_opt__write_procs(list(proc_id), pred_id, pred_info, 
	io__state, io__state).
:- mode trans_opt__write_procs(in, in, in, di, uo) is det.
trans_opt__write_procs([], _, _) --> [].
trans_opt__write_procs([ProcId | ProcIds], PredId, PredInfo) -->
	{ pred_info_procedures(PredInfo, ProcTable) },
	{ map__lookup(ProcTable, ProcId, ProcInfo) },
	{ pred_info_name(PredInfo, PredName) },
	{ pred_info_module(PredInfo, ModuleName) },
	{ pred_info_get_is_pred_or_func(PredInfo, PredOrFunc) },
	{ pred_info_arity(PredInfo, Arity) },
	{ SymName = qualified(ModuleName, PredName) },
	{ proc_info_termination(ProcInfo, Termination) },

	% all predicates to write procedure items into the .trans_opt file
	% should go here.
	termination__output_pragma_opt_terminates(PredOrFunc, SymName,
		Arity, ProcId, Termination),
	
	trans_opt__write_procs(ProcIds, PredId, PredInfo).

%-----------------------------------------------------------------------------%
	% Read in and process the transitive optimization interfaces.

trans_opt__grab_optfiles(Module0, Module, FoundError) -->
	{ Module0 = module_imports(ModuleName, DirectImports0,
		IndirectImports0, Items0, _) },
	{ list__sort_and_remove_dups(DirectImports0, Imports) },
	read_trans_opt_files(Imports, [], OptItems, no, FoundError),
	{ term__context_init(Context) },
	{ varset__init(Varset) },
	{ OptDefn = module_defn(Varset, opt_imported) - Context },
	{ list__append(Items0, [ OptDefn | OptItems ], Items) },
	{ Module = module_imports(ModuleName, DirectImports0, 
		IndirectImports0, Items, no) }.

:- pred read_trans_opt_files(list(module_name), item_list,
	item_list, bool, bool, io__state, io__state).
:- mode read_trans_opt_files(in, in, out, in, out, di, uo) is det.

read_trans_opt_files([], Items, Items, Error, Error) --> [].
read_trans_opt_files([Import | Imports],
		Items0, Items, Error0, Error) -->
	globals__io_lookup_bool_option(very_verbose, VeryVerbose),
	maybe_write_string(VeryVerbose,
		"% Reading transitive optimization interface for module"),
	maybe_write_string(VeryVerbose, " `"),
	maybe_write_string(VeryVerbose, Import),
	maybe_write_string(VeryVerbose, "'... "),
	maybe_flush_output(VeryVerbose),
	maybe_write_string(VeryVerbose, "% done.\n"),

	{ string__append(Import, ".trans_opt", FileName) },
	prog_io__read_module(FileName, Import, yes,
			ModuleError, Messages, Items1),
	update_error_status(ModuleError, Messages, Error0, Error1),
	{ list__append(Items0, Items1, Items2) },
	read_trans_opt_files(Imports, Items2, Items, Error1, Error).

:- pred update_error_status(module_error, message_list, 
	bool, bool, io__state, io__state).
:- mode update_error_status(in, in, in, out, di, uo) is det.

update_error_status(ModuleError, Messages, Error0, Error1) -->
	(
		{ ModuleError = no },
		{ Error1 = Error0 }
	;
		{ ModuleError = yes },
		prog_out__write_messages(Messages),
		{ Error1 = yes }
	;
		{ ModuleError = fatal },
		{ Error1 = Error0 }	
	).
