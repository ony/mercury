%-----------------------------------------------------------------------------%
%
% Copyright (C) 1997 University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% term_errors.m
% Main author: crs.
% 
% This module prints out the various error messages that are produced by
% termination.m
%
%-----------------------------------------------------------------------------%

:- module term_errors.

:- interface.
:- import_module io, hlds_module.
:- import_module bag, std_util, term, list, bool.

% term_errors__output(PredId, ProcId, Module, Success, IO0, IO).
% 	This is used to print out the errors found by termination analysis.
% 	Success returns yes if an error was successfully printed out.
% 	Success will be no if there was no termination error for that
% 	procedure.
:- pred term_errors__output(pred_id, proc_id, module_info, bool,
		io__state, io__state).
:- mode term_errors__output(in, in, in, out, di, uo) is det.


% term_errors__output_const_error(PredId, ProcId, Module, Success, IO0, IO).
% 	This prints out any errors which occured when trying to set the
% 	termination constant.  An error message will only be available if
% 	the termination constant is set to 'inf'.
:- pred term_errors__output_const_error(pred_id, proc_id, module_info, bool,
		io__state, io__state).
:- mode term_errors__output_const_error(in, in, in, out, di, uo) is det.

% This is used to print out error messages for the hlds dumps.  These are
% much more concise than the normal error messages.
:- pred term_errors__output_hlds(pred_id, proc_id, module_info, 
	io__state, io__state).
:- mode term_errors__output_hlds(in, in, in, di, uo) is det.

:- type term_errors__error == pair(term__context, termination_error).
% with these error messages, they do not necessarily need to involve the
% procedure that they are assigned to.  It is possible that an error
% occured when processing other predicates in the same SCC, and therefore
% the termination (or termination constant) were set to dont_know (or
% infinity).  
:- type termination_error
			% a recursive call is made with variables that are 
			% strictly larger than in the head.  note that 
			% the recursive call may be indirect, so this does 
			% not neccessarily indicate non-termination.
			% The first PPId is the calling proc.  The second
			% PPId is the called proc, and the context is the
			% line where the call occurs.
	--->	positive_value(pred_proc_id, pred_proc_id)
	;	horder_call
	;	pragma_c_code
	;	imported_pred
			% dont_know_proc_called(CallerProc, CalleeProc)  
			% A call was made from CallerProc to CalleeProc,
			% where the termination constant of the CalleeProc
			% is set to dont_know.
	;	dont_know_proc_called(pred_proc_id, pred_proc_id)
			% horder_args(CallerProc, CalleeProc)
			% This error message indicates that the CallerProc
			% called the CalleeProc where some of the arguments
			% are of a higher order type.
	;	horder_args(pred_proc_id, pred_proc_id)
	;	inf_termination_const(pred_proc_id, pred_proc_id)
	;	not_subset(pred_proc_id, bag(var), bag(var))
	;	not_dag
	;	no_eqns
	;	lpsolve_failed(eqn_soln)
	;	call_in_single_arg(pred_proc_id)
			% single argument analysis did not find a head
			% variable that was decreasing in size. 
	;	single_arg_failed(term_errors__error)
			% single_arg_failed(ReasonForNormalAnalysisFailing,
			% 	ReasonForSingleArgAnalysisFailing)
	;	single_arg_failed(term_errors__error, term_errors__error)
			% the termination constant of a builtin predicate
			% is set to infinity if the types of the builtin
			% predicate may have a norm greater than 0.
	;	is_builtin.

% eqn_soln are used to report the results from solving the equations
% created in the first pass.  The first 4 (optimal - failure) represent
% output states from lp_solve. 
:- type eqn_soln
	---> 	optimal		
	;	infeasible
	;	unbounded
	;	failure
	;	fatal_error 	% unable to open a file, or make a system call
	;	parse_error	% unable to parse the output from lp_solve
	;	solved(list(pair(pred_proc_id, int))).

:- implementation.

:- import_module hlds_out, prog_out, hlds_pred, passes_aux, require, term_util.

term_errors__output(PredId, ProcId, Module, Success) -->
	{ module_info_pred_proc_info(Module, PredId, ProcId, _, ProcInfo) },
	{ proc_info_termination(ProcInfo, Termination) },
	{ Termination = term(_Const, _Terminates, _UsedArgs, MaybeError) },
	( { MaybeError = yes(Context - Error) } ->
		prog_out__write_context(Context),
		io__write_string("Termination of "),
		hlds_out__write_pred_id(Module, PredId),
		prog_out__write_context(Context),
		io__write_string("  not proved because"),
		{ ConstErrorOutput = no },
		{ ForHLDSDump = no },
		term_errors__output_2(PredId, ProcId, Module, ConstErrorOutput,
			ForHLDSDump, Context - Error),
		{ Success = yes }
	;
		{ Success = no }
	).
	

term_errors__output_const_error(PredId, ProcId, Module, Success) -->
	{ module_info_pred_proc_info(Module, PredId, ProcId, _, ProcInfo) },
	{ proc_info_termination(ProcInfo, Termination) },
	{ Termination = term(Const, _Terminates, _UsedArgs, _MaybeError) },
	( { Const = inf(Context - Error) } ->
		prog_out__write_context(Context),
		io__write_string("Termination constant of "),
		hlds_out__write_pred_id(Module, PredId),
		prog_out__write_context(Context),
		io__write_string("  set to infinity because "),
		{ ConstErrorOutput = yes },
		{ ForHLDSDump = no },
		term_errors__output_2(PredId, ProcId, Module, ConstErrorOutput,
			ForHLDSDump, Context - Error),
		{ Success = yes }
	; 
		{ Success = no }
	).

term_errors__output_hlds(PredId, ProcId, Module) -->
	{ module_info_pred_proc_info(Module, PredId, ProcId, _, ProcInfo) },
	{ proc_info_termination(ProcInfo, Termination) },
	{ Termination = term(Const, _Terminates, _UsedArgs, MaybeError) },
	{ ForHLDSDump = yes },
	( { MaybeError = yes(TermContext - TermError) } ->
		io__write_string("% "),
		prog_out__write_context(TermContext),
		io__write_string("Termination not proved because "),
		{ ConstErrorOutput0 = no },
		term_errors__output_2(PredId,ProcId, Module, ConstErrorOutput0,
			ForHLDSDump, TermContext - TermError)
	;
		[]
	),
	( { Const = inf(ConstContext - ConstError) } ->
		io__write_string("% "),
		prog_out__write_context(ConstContext),
		io__write_string("Termination const set to inf as "),
		{ ConstErrorOutput1 = yes },
		term_errors__output_2(PredId, ProcId, Module, ConstErrorOutput1,
			ForHLDSDump, ConstContext - ConstError)
	;
		[]
	).
	

:- pred term_errors__output_same_SCC(pred_id, module_info, term__context,
	bool, io__state, io__state).
:- mode term_errors__output_same_SCC(in, in, in, in, di, uo) is det.
term_errors__output_same_SCC(PredId, Module, Context, ForHLDSDump) -->
	io__write_string("it is in the same SCC as the\n"),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string("  "),
	hlds_out__write_pred_id(Module, PredId).


% term_errors__output_2(PredId, ProcId, Module, ConstErrorOutput,
% 	ForHLDSDump, Error, IO0, IO).
% If this predicate is called from term_errors__output_const_error, then
% ConstErrorOutput should be set to `yes' to indicate that the error
% message should describe why the constant was set to infinity.
% If ConstErrorOutput is set to `no' then term_errors__output_2 describes
% why the analysis could not prove termination.
%
% If ForHLDSDump is set to yes, then a % must be placed at the beginning of
% each line, because the output is for the HLDS dump.
% 
% This predicate is used by both term_errors__output() and
% term_errors__output_const_error() to print out the reason for the error.
% When these predicates are called they are preceded by: (for example)
% myfile.m:300: Termination of predicate `myfile:yourpredicate/3' 
% myfile.m:300:   not proved because 
%
% or by
%
% myfile.m:300: Termination constant of function `myfile:myfunction/6' 
% myfile.m:300:   set to infinity because 
%
:- pred term_errors__output_2(pred_id, proc_id, module_info, bool, bool,
	term_errors__error, io__state, io__state).
:- mode term_errors__output_2(in, in, in, in, in, in, di, uo) is det.
term_errors__output_2(PredId, _ProcId, Module, _ConstErrorOutput, ForHLDSDump,
		Context - positive_value(CallerPPId, CalledPPId)) -->	
	{ CalledPPId = proc(CalledPredId, _CalledProcId) },
	{ CallerPPId = proc(CallerPredId, _CallerProcId) },
	( { PredId = CallerPredId } ->
		io__write_string("it contains a\n")
	;
		term_errors__output_same_SCC(PredId, Module, Context, 
			ForHLDSDump),
		io__write_string(" which contains a\n")
	),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	( { PredId = CalledPredId } ->
		io__write_string("  directly recursive call")
	;
		io__write_string("  recursive call to"),
		hlds_out__write_pred_id(Module, CalledPredId),
		io__nl,
		maybe_write_string(ForHLDSDump, "% "),
		prog_out__write_context(Context),
		io__write_string("  ")
	),
	io__write_string("with the size of the variables increased.\n").

term_errors__output_2(_PredId, _ProcId, _Module, _ConstErrOutput, _ForHLDSDump,
		_Context - horder_call) -->
	io__write_string("it contains a higher order call\n").

term_errors__output_2(_PredId, _ProcId, _Module, _ConstErrOutput, _ForHLDSDump,
		_Context - pragma_c_code) -->
	io__write_string("it contains a pragma c_code() declaration\n").

term_errors__output_2(PredId, _ProcId, Module, _ConstErrorOutput, ForHLDSDump,
		Context - dont_know_proc_called(CallerPPId, CalleePPId)) -->
	{ CallerPPId = proc(CallerPredId, _CallerProcId) },
	{ CalleePPId = proc(CalleePredId, _CalleeProcId) },
	( { PredId = CallerPredId } ->
		io__write_string("it calls the ")
	;
		term_errors__output_same_SCC(CallerPredId, Module, Context,
			ForHLDSDump),
		io__write_string("which calls the ")
	),
	hlds_out__write_pred_id(Module, CalleePredId),
	io__nl,
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string("  which could not be proved to terminate\n").

term_errors__output_2(_PredId, _ProcId, _Module, _ConstErrOutput, _ForHLDSDump,
		_Context - imported_pred) -->
	io__write_string("it was imported.").

term_errors__output_2(PredId, _ProcId, Module, _ConstErrorOutput, ForHLDSDump,
		Context - horder_args(CallerPPId, CalleePPId)) -->
	% OtherPPId may refer to the current Predicate, or it may refer to
	% another predicate in the same SCC
	{ CallerPPId = proc(CallerPredId, _CallerProcId) },
	{ CalleePPId = proc(CalleePredId, _CalleeProcId) },

	( { PredId = CallerPredId } ->
		io__write_string("it calls the")
	;
		term_errors__output_same_SCC(CallerPredId, Module, Context,
			ForHLDSDump),
		io__write_string("which calls the")
	),
	hlds_out__write_pred_id(Module, CalleePredId),
	io__nl,
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string(
		"  where the call contains higher order argument(s)\n").

term_errors__output_2(PredId, _ProcId, Module, _ConstErrorOutput, ForHLDSDump,
		Context - inf_termination_const(CallerPPId, CalleePPId)) -->
	{ CallerPPId = proc(CallerPredId, _CallerProcId) },
	{ CalleePPId = proc(CalleePredId, CalleeProcId) },
	( { PredId = CallerPredId } ->
		io__write_string("it calls the")
	;
		term_errors__output_same_SCC(CallerPredId, Module, Context,
			ForHLDSDump),
		io__write_string("which calls the")
	),
	hlds_out__write_pred_id(Module, CalleePredId),
	io__nl,
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string(
		"  which has a termination constant of infinity\n"),
	term_errors__output_const_error(CalleePredId, CalleeProcId, Module,
		Success),
	{ ( Success = yes ->
		true
	;
		error("term_errors:output_2 Unexpected return value from term_errors:output_const_error/6")
	) }.

% If hlds dump, should print out variables in numerical form
% If verbose errors requested (-E), should list variables
term_errors__output_2(PredId, _ProcId, Module, ConstErrorOutput, ForHLDSDump,
		Context - not_subset(OtherPPId, _Vars1, _Vars2)) -->
	{ OtherPPId = proc(OtherPredId, _OtherProcId) },
	{ module_info_pred_info(Module, OtherPredId, OtherPredInfo) },
	{ pred_info_get_is_pred_or_func(OtherPredInfo, OtherPredOrFunc) },
	( { OtherPredId = PredId } ->
		[]
	;
		term_errors__output_same_SCC(OtherPredId, Module, Context,
			ForHLDSDump),
		( { ConstErrorOutput = yes } ->
			io__write_string(
				". The termination constant of that\n"),
			maybe_write_string(ForHLDSDump, "% "),
			prog_out__write_context(Context),
			io__write_string("  "),
			hlds_out__write_pred_or_func(OtherPredOrFunc),
			io__write_string(" was set to infinity because ")
		;
			io__write_string(". Termination of that\n"),
			maybe_write_string(ForHLDSDump, "% "),
			prog_out__write_context(Context),
			io__write_string("  "),
			hlds_out__write_pred_or_func(OtherPredOrFunc),
			io__write_string(" could not be proved because ")
		)
	),
	io__write_string("the analysis\n"),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string("  found that the set of"),
	( { ConstErrorOutput = yes } ->
		io__write_string(" output supplier variables\n")
	;
		io__write_string(" recursive input supplier variables\n")
	),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string("  was not a subset of the head variables of the "),
	hlds_out__write_pred_or_func(OtherPredOrFunc),
	io__write_string(".\n").
	

term_errors__output_2(_PredId, _ProcId, _Module, _ConstErrorOutput, ForHLDSDump,
		Context - not_dag) -->
	io__write_string("there was a cycle in the call graph of\n"),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string(
		"this SCC where the variables did not decrease in size\n").


term_errors__output_2(_PredId, _ProcId, _Module, _ConstErrorOutput, ForHLDSDump,
		Context - no_eqns)-->
	io__write_string("the analysis was unable to form any\n"),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string(
		"  constraints between the arguments of the predicates\n"),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string("  and functions in this SCC\n").


term_errors__output_2(_PredId, _ProcId, _Module, _ConstErrorOutput, ForHLDSDump,
		Context - lpsolve_failed(Reason)) -->
	io__write_string("the constraint solver "),
	(
 		{ Reason = optimal },
		{ error("term_errors:output_2 Unexpected return value from lp_solve") }
	;
		{ Reason = infeasible },
		io__write_string("found the\n"),
		maybe_write_string(ForHLDSDump, "% "),
		prog_out__write_context(Context),
		io__write_string("  constraints that the analysis produced to be infeasible\n")
	;
		{ Reason = unbounded },
		io__write_string("found that the\n"),
		maybe_write_string(ForHLDSDump, "% "),
		prog_out__write_context(Context),
		io__write_string(
			"  constraints were not strong enough to put a\n"),
		maybe_write_string(ForHLDSDump, "% "),
		prog_out__write_context(Context),
		io__write_string(
			"  bound on the value of the change constants\n")
	;
		{ Reason = failure },
		io__write_string("was unable to\n"),
		maybe_write_string(ForHLDSDump, "% "),
		prog_out__write_context(Context),
		io__write_string(
			"  solve the constraints that were produced\n")
	;
		{ Reason = fatal_error },
		io__set_exit_status(1),
		io__write_string("was unable to create and/or\n"),
		maybe_write_string(ForHLDSDump, "% "),
		prog_out__write_context(Context),
		io__write_string("  remove the temporary files it required\n")
	;
		{ Reason = parse_error },
		{ error("term_errors:output_2 Unexpected return value from lp_solve") }
	;
		{ Reason = solved(_) },
		{ error("term_errors:output_2 Unexpected return value from lp_solve") }
	).

term_errors__output_2(_PredId, _ProcId, Module, _ConstErrorOutput, ForHLDSDump,
		Context - call_in_single_arg(PPId)) -->
	{ PPId = proc(CallPredId, _CallProcId) },
	io__write_string("single argument analysis encountered\n"),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string("  a call to "),
	hlds_out__write_pred_id(Module, CallPredId),
	io__write_string("that could not be processed\n").

term_errors__output_2(PredId, ProcId, Module, ConstErrorOutput, ForHLDSDump,
		Context - single_arg_failed(Error)) -->
	term_errors__output_2(PredId, ProcId, Module, ConstErrorOutput, 
		ForHLDSDump, Error),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string(
		"  Single argument analysis failed to find a head variable\n"),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(Context),
	io__write_string("  that was always decreasing in size.\n").

term_errors__output_2(PredId, ProcId, Module, ConstErrorOutput, ForHLDSDump, 
		_DummyContext - single_arg_failed(NormalError, 
		SingleArgContext - SingleArgError)) -->

		% single argument analysis is independent of finding the
		% termination constant.  The error for a termination
		% constant should never be single_arg_failed.
	{ require(unify(ConstErrorOutput, no),
		"Unexpected value in term_errors__output_2") },

	term_errors__output_2(PredId, ProcId, Module, ConstErrorOutput, 
		ForHLDSDump, NormalError),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(SingleArgContext),
	io__write_string("  Single argument termination analysis failed to\n"),
	maybe_write_string(ForHLDSDump, "% "),
	prog_out__write_context(SingleArgContext),
	io__write_string("  prove termination because "),
	term_errors__output_2(PredId, ProcId, Module, ConstErrorOutput, 
		ForHLDSDump, SingleArgContext - SingleArgError).

term_errors__output_2(_PredId, _ProcId, _Module, ConstErrorOutput, _ForHldsDump,
		_Context - is_builtin) -->
	{ require(unify(ConstErrorOutput, yes), 
		"Unexpected value in term_errors:output_2") },
	io__write_string("it is a builtin predicate\n").


