%-----------------------------------------------------------------------------
%
% Copyright (C) 1997 University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------
%
% termination.m
% Main author: crs.
%
% This termination analysis is based on the algorithm given by Gerhard Groeger
% and Lutz Plumer in their paper "Handling of Mutual Recursion in Automatic 
% Termination Proofs for Logic Programs"  which was printed in JICSLP '92
% (the proceedings of the Joint International Conference and Symposium on
% Logic Programming 1992) pages 336 - 350.
%
% Currently, this implementation assumes that all c_code terminates.
% It also fails to prove termination for any predicate that involves higher
% order calls.
% 			
%-----------------------------------------------------------------------------

:- module termination.

:- interface.

:- import_module io.
:- import_module hlds_module, term_util.

% The top level predicate.  This controls all of the termination analysis
:- pred termination__pass(module_info, module_info, io__state, io__state).
:- mode termination__pass(in, out, di, uo) is det.

% This predicate provides an initialised termination structure.
:- pred termination__init(termination).
:- mode termination__init(out) is det.

% This predicate prints out a termination structure.
:- pred termination__out(termination, io__state, io__state).
:- mode termination__out(in, di, uo) is det.

% This predicate prints out the used_args structure
:- pred termination__out_used_args(termination, io__state, io__state). 
:- mode termination__out_used_args(in, di, uo) is det.

% This predicate prints out the termination constant
:- pred termination__out_const(termination, io__state, io__state).
:- mode termination__out_const(in, di, uo) is det.

% This predicate prints out the terminates (yes/dont_know/not_set).
:- pred termination__out_terminates(termination, io__state, io__state).
:- mode termination__out_terminates(in, di, uo) is det.

% This predicate outputs pragma opt_terminates which are used in .trans_opt
% and .opt files.
:- pred termination__output_pragma_opt_terminates(pred_or_func, sym_name,
	int, proc_id, termination, io__state, io__state).
:- mode termination__output_pragma_opt_terminates(in, in, in, in, in, 
	di, uo) is det.

% This is used to output an error in a short form, suitable for 
% printing the HLDS.
:- pred termination__maybe_output_error(module_info, termination, 
	io__state, io__state).
:- mode termination__maybe_output_error(in, in, di, uo) is det.

%----------------------------------------------------------------------------%

:- implementation.

:- import_module map, std_util, list, type_util, require.
:- import_module options, globals, bool, char, prog_data.
:- import_module passes_aux. 	% for maybe_write_string
:- import_module mercury_to_mercury.
:- import_module inst_match, mode_util, int, hlds_out, string, relation.
:- import_module hlds_data, hlds_pred, hlds_goal, dependency_graph.
:- import_module code_util, prog_out, bag, set.
:- import_module term_pass1, term_pass2, term_errors.

%-----------------------------------------------------------------------------%

termination__pass(Module0, Module) -->
	globals__io_lookup_bool_option(verbose, Verbose),
	maybe_write_string(Verbose, "% Checking termination...\n"),
	{ module_info_ensure_dependency_info(Module0, Module1) },
	{ module_info_predids(Module1, PredIds) },

	% process builtin predicates
	check_preds(PredIds, Module1, Module2),

	proc_inequalities(Module2, Module3),

	termination(Module3, Module),

	/**
	% to output opt_terminates pragmas to .opt files, uncomment this
	% block of code.
	globals__io_lookup_bool_option(make_optimization_interface,
		MakeOptInt),
	( { MakeOptInt = yes } ->
		termination__make_opt_int(PredIds, Module)
	;
		[]
	),
	**/

	maybe_write_string(Verbose, "% Termination checking done.\n").

% An initialised termination structure.
termination__init(term(not_set, not_set, no, no)).

%-----------------------------------------------------------------------------%
% These termination__out predicates are used to print out the opt_terminates
% pragmas.  If they are changed, then prog_io_pragma.m must also be changed 
% so that it can parse the resulting pragma opt_terminates declarations.
% XXX could these predicates be replaced by calls to io__write?

termination__out(Termination) -->
	termination__out_terminates(Termination),
	io__write_string("("),
	termination__out_const(Termination),
	io__write_string(")").

termination__out_used_args(term(_Const, _Term, MaybeUsedArgs, _)) -->
	( 	
		{ MaybeUsedArgs = yes([]) },
		io__write_string("yes([])") 
	;
		{ MaybeUsedArgs = yes([UsedArg | UsedArgs]) },
		io__write_string("yes([ "),
		io__write(UsedArg),
		termination__out_used_args_2(UsedArgs),
		io__write_string(" ])")
	;
		{ MaybeUsedArgs = no }, 
		io__write_string("no")
	).

:- pred termination__out_used_args_2(list(bool), io__state, io__state). 
:- mode termination__out_used_args_2(in, di, uo) is det.
termination__out_used_args_2([]) --> [].
termination__out_used_args_2([ UsedArg | UsedArgs ]) -->
	io__write_string(", "),
	io__write(UsedArg),
	termination__out_used_args_2(UsedArgs).

termination__out_terminates(term(_, Term, _, _)) -->
	termination__out_terminates_2(Term).

:- pred termination__out_terminates_2(terminates, io__state, io__state).
:- mode termination__out_terminates_2(in, di, uo) is det.
termination__out_terminates_2(not_set) --> 
	io__write_string("not_set").
termination__out_terminates_2(dont_know) --> 
	io__write_string("dont_know").
termination__out_terminates_2(yes) --> 
	io__write_string("yes").

termination__out_const(term(Const, _, _, _)) --> 
	termination__out_const_2(Const).

:- pred termination__out_const_2(term_util__constant, io__state, io__state).
:- mode termination__out_const_2(in, di, uo) is det.
termination__out_const_2(inf(_)) -->
	io__write_string("infinite").
termination__out_const_2(not_set) -->
	io__write_string("not_set").
termination__out_const_2(set(Int)) -->
	io__write_string("set("),
	io__write_int(Int),
	io__write_string(")").

termination__output_pragma_opt_terminates(PredOrFunc, SymName,
		Arity, ProcId, Termination) -->
	io__write_string(":- pragma opt_terminates("),
	hlds_out__write_pred_or_func(PredOrFunc),
	io__write_string(", "),
	mercury_output_bracketed_sym_name(SymName),
	io__write_string(", "),
	io__write_int(Arity),
	io__write_string(", "),
	{ proc_id_to_int(ProcId, ProcInt) },
	io__write_int(ProcInt),
	io__write_string(", "),
	termination__out_const(Termination),
	io__write_string(", "),
	termination__out_terminates(Termination),
	io__write_string(", "),
	termination__out_used_args(Termination),
	io__write_string(").\n").
	
termination__maybe_output_error(Module, term(Const, _, _, MaybeError)) -->
	( { MaybeError = yes(Error) } ->
		io__write_string("% unable to prove termination because:"),
		term_errors__output(no, Module, Error)
	;
		[]
	),
	( { Const = inf(yes(ConstError)) } ->
		io__write_string("% unable to set termination const because:"),
		term_errors__output(no, Module, ConstError)
	;
		[]
	).

%-----------------------------------------------------------------------------%

:- pred check_preds(list(pred_id), module_info, module_info, 
	io__state, io__state).
:- mode check_preds(in, in, out, di, uo) is det.

% This predicate processes each predicate and sets the termination property
% if possible.  This is done as follows:  Set the termination to yes if:
% - there is a terminates pragma defined for the predicate
% - there is a `check_termination' pragma defined for the predicate, and it
% 	is imported, and the compiler is not currently generating the
% 	intermodule optimization file.
% - the predicate is a builtin predicate or is compiler generated (This
% 	also sets the termination constant and UsedArgs).
%
% Set the termination to dont_know if:
% - the predicate is imported and there is no other source of information
% 	about it (opt_terminates pragmas, terminates pragmas,
% 	check_termination pragmas, builtin/compiler generated).
check_preds([], Module, Module, State, State).
check_preds([PredId | PredIds] , Module0, Module, State0, State) :-
	module_info_preds(Module0, PredTable0),
	map__lookup(PredTable0, PredId, PredInfo0),
	pred_info_import_status(PredInfo0, ImportStatus),
	pred_info_procedures(PredInfo0, ProcTable0),
	map__keys(ProcTable0, ProcIds),
	(
		( ImportStatus = exported
		; ImportStatus = local
		; ImportStatus = pseudo_exported
		)
	->
		pred_info_get_marker_list(PredInfo0, Markers),
		( list__member(request(terminates), Markers) ->
			MaybeFind = no,
			ReplaceTerminate = yes,
			MaybeError = no,
			change_procs_terminate(ProcIds, MaybeFind, 
				ReplaceTerminate, MaybeError, 
				ProcTable0, ProcTable2)
		; code_util__predinfo_is_builtin(PredInfo0) ->
			set_builtin_terminates(ProcIds, PredInfo0, Module0,
				ProcTable0, ProcTable2)
		;
			ProcTable2 = ProcTable0
		),
		State0 = State1
	; %else if
		( ImportStatus = imported
		; ImportStatus = opt_imported
		; ImportStatus = pseudo_imported  % should this be here?
		)
	->
		% All of the predicates that are processed in this section
		% are imported in some way.
		% With imported predicates, any 'check_termination'
		% pragmas will be checked by the compiler when it compiles
		% relevant source file (that the pred was imported from).
		% When making the intermodule optimizations, the 
		% check_termination will not be checked when the relevant
		% source file is compiled, so it cannot be depended upon. 
		pred_info_get_marker_list(PredInfo0, Markers),
		globals__io_lookup_bool_option(make_optimization_interface,
			MakeOptInt, State0, State1),
		(
		    (
			list__member(request(terminates), Markers)
		    ; 
			MakeOptInt = no,
			list__member(request(check_termination), Markers)
		    )
		->
			change_procs_terminate(ProcIds, no, yes, no, 
				 ProcTable0, ProcTable1)
		; %else if
		    	code_util__predinfo_is_builtin(PredInfo0)
		->
			set_builtin_terminates(ProcIds, PredInfo0, Module0,
				ProcTable0, ProcTable1)
		;
			% go through, changing each 'not_set' to 'dont_know'
			MaybeFind = yes(not_set),
			ReplaceTerminate = dont_know,
			MaybeError = no,
			change_procs_terminate(ProcIds, MaybeFind,
				ReplaceTerminate, MaybeError, ProcTable0,
				ProcTable1)
				
		),
		MaybeFindConst = yes(not_set),
		MaybeConstError = no,
		ReplaceConst = inf(MaybeConstError),
		change_procs_const(ProcIds, MaybeFindConst, ReplaceConst,
			ProcTable1, ProcTable2)
	;
%		( ImportStatus = abstract_imported
%		; ImportStatus = abstract_exported
%		),
		% This should not happen, as procedures are being processed
		% here, and these import_status' refer to abstract types.
		error("termination__check_preds: Unexpected import status of a predicate")
	),
	( 
		% It is possible for compiler generated/mercury builtin
		% predicates to be imported or locally defined, so they
		% must be covered here, seperatly.
		set_compiler_gen_terminates(ProcIds, PredInfo0, 
			Module0, ProcTable2, ProcTable3)
	->
		ProcTable = ProcTable3
	;
		ProcTable = ProcTable2
	),
	pred_info_set_procedures(PredInfo0, ProcTable, PredInfo),
	map__set(PredTable0, PredId, PredInfo, PredTable),
	module_info_set_preds(Module0, PredTable, Module1),
	check_preds(PredIds, Module1, Module, State1, State).

% The list of proc_ids must refer to builtin predicates.  This predicate
% sets the termination information of builtin predicates.
% XXX this should be called from set_compiler_gen_terminates instead of
% from check_preds.
:- pred set_builtin_terminates(list(proc_id), pred_info, module_info, 
	proc_table, proc_table).
:- mode set_builtin_terminates(in, in, in, in, out) is det.
set_builtin_terminates([], _, _, ProcTable, ProcTable).
set_builtin_terminates([ProcId | ProcIds], PredInfo, Module, ProcTable0, 
			ProcTable) :-
	map__lookup(ProcTable0, ProcId, ProcInfo0), 
	( attempt_set_proc_const(Module, PredInfo, ProcInfo0) ->
		% For attempt_set_proc_const to succeed on a procedure, the
		% output variables of that procedure must all be of a type
		% whose norm will be zero.  Hence the size of the output
		% variables will all be 0, independent of the size of the
		% input variables.  Therefore, as the size of the output
		% variables do not depend on the size of the input
		% variables, UsedArgs should be set to yes([no, no, ...]).
		Const = set(0),
		proc_info_headvars(ProcInfo0, HeadVars),
		term_util__make_bool_list(HeadVars, [], Bools),
		UsedArgs = yes(Bools)
	;
		Const = inf(no),
		UsedArgs = no
	),
	Term = term(Const, yes, UsedArgs, no),
	proc_info_set_termination(ProcInfo0, Term, ProcInfo),
	map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable1),
	set_builtin_terminates(ProcIds, PredInfo, Module, ProcTable1, 
		ProcTable).

% This predicate checks each ProcId in the list to see if it is a compiler
% generated predicate, or a mercury_builtin predicate.  If it is, then the
% compiler sets the termination property of the ProcIds accordingly.
:- pred set_compiler_gen_terminates(list(proc_id), pred_info, module_info,
	proc_table, proc_table).
:- mode set_compiler_gen_terminates(in, in, in, in, out) is semidet.
set_compiler_gen_terminates([], _PredInfo, _Module, ProcTable, ProcTable).
set_compiler_gen_terminates([ ProcId | ProcIds ], PredInfo, Module, 
		ProcTable0, ProcTable) :-
	pred_info_name(PredInfo, PredName),
	pred_info_arity(PredInfo, Arity),
	pred_info_module(PredInfo, ModuleName),
	map__lookup(ProcTable0, ProcId, ProcInfo0),
	( Arity = 3 ->
		(
			PredName = "__Compare__"
		;
			ModuleName = "mercury_builtin",
			PredName = "compare"
		),
		proc_info_headvars(ProcInfo0, HeadVars),
		term_util__make_bool_list(HeadVars,
			[no, no, no], OutList),
		Termination = term(set(0), yes, yes(OutList), no)
	; Arity = 2 ->
		(
			(
				PredName = "__Unify__"
			;
				ModuleName = "mercury_builtin",
				PredName = "unify"
			)
		->
			proc_info_headvars(ProcInfo0, HeadVars),
			term_util__make_bool_list(HeadVars,
				[yes, yes], OutList),
			Termination = term(set(0), yes,
				yes(OutList), no)
		; % else if
			( 
				PredName = "__Index__"
			;
				ModuleName = "mercury_builtin",
				PredName = "index"
			)
		->
			proc_info_headvars(ProcInfo0, HeadVars),
			term_util__make_bool_list(HeadVars,
				[no, no], OutList),
			Termination = term(set(0), yes,
				yes(OutList), no)
		; % else 
			% XXX what is the relationship between size of
			% input and size of output in Term_To_Type and
			% Type_To_Term?  Which arguments are used to make
			% the output variables?
			( PredName = "__Term_To_Type__"
			; PredName = "__Type_To_Term__"
			),
			Termination = term(inf(no), yes, no, no)
		)
	;
		ModuleName = "mercury_builtin",
		( attempt_set_proc_const(Module, PredInfo, ProcInfo0) ->
			proc_info_headvars(ProcInfo0, HeadVars),
			term_util__make_bool_list(HeadVars, [], Bools),
			UsedArgs = yes(Bools),
			Termination = term(set(0), yes, UsedArgs, no)
		;
			proc_info_termination(ProcInfo0, OldTerm),
			OldTerm = term(OldConst, _, OldUsedArgs, _),
			Termination = term(OldConst, yes, OldUsedArgs, no)
		)
	),
	% The procedure is a compiler generated procedure, so enter the
	% data in the proc_info.
	proc_info_set_termination(ProcInfo0, Termination, ProcInfo),
	map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable1),
	set_compiler_gen_terminates(ProcIds, PredInfo, Module,
		ProcTable1, ProcTable).

% For attempt_set_proc_const to succeed, the output variables of
% that procedure must all be of a type that will always have a norm of 0.
% Hence the size of the output vars will always be 0, independent of the
% size of the input variables. 
:- pred attempt_set_proc_const(module_info, pred_info, proc_info).
:- mode attempt_set_proc_const(in, in, in) is semidet.
attempt_set_proc_const(Module, PredInfo, ProcInfo) :-
	pred_info_arg_types(PredInfo, _, TypeList),
	proc_info_argmodes(ProcInfo, ModeList),
	attempt_set_proc_const_2(TypeList, ModeList, Module). 

:- pred attempt_set_proc_const_2(list(type), list(mode), module_info).
:- mode attempt_set_proc_const_2(in, in, in) is semidet.
attempt_set_proc_const_2([], [], _).
attempt_set_proc_const_2([], [_|_], _) :- 
	error("termination__attempt_set_proc_const_2: Unmatched variables.").
attempt_set_proc_const_2([_|_], [], _) :- 
	error("termination:attempt_set_proc_const_2: Unmatched variables").
attempt_set_proc_const_2([Type | Types], [Mode | Modes], Module) :-
	( mode_is_input(Module, Mode) ->
		% The variable is an input variables, so its size is
		% irrelevant.
		attempt_set_proc_const_2(Types, Modes, Module)
	;
		classify_type(Type, Module, TypeCategory),
		% User_type could be a type_info, which should be called
		% size 0.  This is not a big problem, as most type_infos
		% are input.
		TypeCategory \= user_type(_), 
		% This could be changed, by looking up the polymorphic type, 
		% and seeing if it is recursive, or could it?
		TypeCategory \= polymorphic_type, 
		TypeCategory \= pred_type,
		attempt_set_proc_const_2(Types, Modes, Module)
	).
		
% This predicate changes the terminate part of a list of procedures.
% change_procs_terminate(ProcList,MaybeFind, Replace, MaybeError,
% 		ProcTable, ProcTable).
% If MaybeFind is no, then this predicate changes the terminates and
% MaybeError field of all the procedures passed to it.  If MaybeFind is set
% to yes(OldTerminates) then the terminates and MaybeError field of a
% procedure is only changed if the Terminates field was OldTerminates.
:- pred change_procs_terminate(list(proc_id), maybe(terminates), terminates,
	maybe(term_errors__error), proc_table, proc_table).
:- mode change_procs_terminate(in, in, in, in, in, out) is det.
change_procs_terminate([], _Find, _Replace, _, ProcTable, ProcTable).
change_procs_terminate([ProcId | ProcIds], MaybeFind, Replace, MaybeError, 
		ProcTable0, ProcTable) :-
	map__lookup(ProcTable0, ProcId, ProcInfo0),
	proc_info_termination(ProcInfo0, Termination),
	( 
		Termination = term(Const, Terminates, UsedArgs, _Error),
		( 
			MaybeFind = yes(Terminates)
		;
			MaybeFind = no
		)

	->
		Termination1 = term(Const, Replace, UsedArgs, MaybeError),
		proc_info_set_termination(ProcInfo0, Termination1, ProcInfo),
		map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable1)
	;
		ProcTable1 = ProcTable0
	),
	change_procs_terminate(ProcIds, MaybeFind, Replace, MaybeError,
		ProcTable1, ProcTable).

% This predicate changes the termination constant of a list of procedures.
% change_procs_const(ProcList,MaybeFind, Replace, ProcTable, ProcTable).
% If MaybeFind is no, then this predicate changes the constant
% field of all the procedures passed to it.  If MaybeFind is set
% to yes(OldConst) then the termination constant of a procedure is
% only changed if the Constant field was OldConst.
:- pred change_procs_const(list(proc_id), maybe(term_util__constant),
	term_util__constant, proc_table, proc_table).
:- mode change_procs_const(in, in, in, in, out) is det.
change_procs_const([], _Find, _Replace, ProcTable, ProcTable).
change_procs_const([ProcId | ProcIds], MaybeFind, Replace, ProcTable0, 
		ProcTable) :-
	map__lookup(ProcTable0, ProcId, ProcInfo0),
	proc_info_termination(ProcInfo0, Termination),
	( 
		Termination = term(Const, Term, UsedArgs, MaybeError),
		(
			MaybeFind = yes(Const)
		;
			MaybeFind = no
		)
	->
		Termination1 = term(Replace, Term, UsedArgs, MaybeError),
		proc_info_set_termination(ProcInfo0, Termination1, ProcInfo),
		map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable1)
	;
		ProcTable1 = ProcTable0
	),
	change_procs_const(ProcIds, MaybeFind, Replace, ProcTable1, ProcTable).


%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
% These predicates are used to add the opt_terminates pragmas to the .opt
% file.  Currently they are not used, because the .trans_opt file gives
% much better accuracy.  The two files are not mutually exclusive, and
% termination information may be stored in both.

:- pred termination__make_opt_int(list(pred_id), module_info, io__state, 
		io__state).
:- mode termination__make_opt_int(in, in, di, uo) is det.
termination__make_opt_int(PredIds, Module) -->
	{ module_info_name(Module, ModuleName) },
	{ string__append(ModuleName, ".opt", OptFileName) },
	io__open_append(OptFileName, OptFileRes),
	( { OptFileRes = ok(OptFile) } ->
		io__set_output_stream(OptFile, OldStream),
		termination__make_opt_int_2(PredIds, Module),
		io__set_output_stream(OldStream, _),
		io__close_output(OptFile)
	;
		% damn thing
		io__write_strings(["Cannot open `",
			OptFileName, "' for output\n"]),
		io__set_exit_status(1)
	).

:- pred termination__make_opt_int_2(list(pred_id), module_info, 
	io__state, io__state).
:- mode termination__make_opt_int_2(in, in, di, uo) is det.
termination__make_opt_int_2([], _Module) --> [].
termination__make_opt_int_2([ PredId | PredIds ], Module) -->
	{ module_info_preds(Module, PredTable) },
	{ map__lookup(PredTable, PredId, PredInfo) },
	{ pred_info_import_status(PredInfo, ImportStatus) },
	{ pred_info_procedures(PredInfo, ProcTable) },
	{ pred_info_procids(PredInfo, ProcIds) },
	{ pred_info_get_is_pred_or_func(PredInfo, PredOrFunc) },
	{ pred_info_name(PredInfo, PredName) },
	{ pred_info_module(PredInfo, ModuleName) },
	{ SymName = qualified(ModuleName, PredName) },
	{ pred_info_arity(PredInfo, Arity) },

	( { ImportStatus = exported } ->
		termination__make_opt_int_3(PredId, ProcIds, ProcTable, 
			PredOrFunc, SymName, Arity)
	;
		[]
	),
	termination__make_opt_int_2(PredIds, Module).
	
:- pred termination__make_opt_int_3(pred_id, list(proc_id), proc_table,
	pred_or_func, sym_name, arity, io__state, io__state).
:- mode termination__make_opt_int_3(in, in, in, in, in, in, di, uo) is det.
termination__make_opt_int_3(_PredId, [], _, _, _, _) --> [].
termination__make_opt_int_3(PredId, [ ProcId | ProcIds ], ProcTable, 
		PredOrFunc, SymName, Arity) -->
	{ map__lookup(ProcTable, ProcId, ProcInfo) },
	{ proc_info_termination(ProcInfo, Termination) },
	termination__output_pragma_opt_terminates(PredOrFunc, SymName,
		Arity, ProcId, Termination),
	termination__make_opt_int_3(PredId, ProcIds, ProcTable, PredOrFunc, 
		SymName, Arity).

