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
:- import_module bag, std_util, term, list.

% This pred currently has 2 purposes.  The first is for printing normal error
% messages.  These are printed if a pragma check_termination has been
% defined for that predicate.  If so, then term_errors__output should be
% called with the first argument as yes(PredId) where PredId is the
% predicate that had the check_termination pragma defined for it.  By
% calling it this way, the error messages that are printed out are much
% more detailed.  The other use is in printing out the HLDS, this is done
% by setting the first argument to no, which causes a much more concise
% printout.  Perhaps it would be better to have 2 seperate predicates
:- pred term_errors__output(maybe(pred_id), module_info, 
	term_errors__error, io__state, io__state).
:- mode term_errors__output(in, in, in, di, uo) is det.

:- type term_errors__error == pair(term__context, termination_error).
:- type termination_error
	--->	positive_value(pred_proc_id, pred_proc_id)
			% a recursive call is made with variables that are 
			% strictly larger than in the head.  note that 
			% the recursive call may be indirect, so this does 
			% not neccessarily indicate non-termination.
			% The first PPId is the calling proc.  The second
			% PPId is the called proc, and the context is the
			% line where the call occurs.
	;	not_subset(bag(var), bag(var))
	;	horder_call
	;	pragma_c_code
	;	dont_know_proc(pred_proc_id)
	;	dont_know_proc_called(pred_proc_id)
	;	horder_args(pred_proc_id)
	;	inf_termination_const(pred_proc_id)
	;	ite_wrong_vars(bag(var), bag(var))
	;       switch_wrong_vars(bag(var), bag(var))
	;       disj_wrong_vars(bag(var), bag(var))
	;	not_dag
	;	no_eqns
	;	lpsolve_failed(eqn_soln)
	;	call_in_single_arg(pred_proc_id)
	;	single_arg_failed(term_errors__error)
	;	single_arg_failed(term_errors__error, term_errors__error).

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

:- import_module hlds_out, prog_out, hlds_pred.

term_errors__output(MaybePredId, Module, 
		Context - positive_value(CallerPPId, CalledPPId)) -->	
	( { MaybePredId = yes(PredId) } ->
		{ CalledPPId = proc(CalledPredId, _CalledProcId) },
		{ CallerPPId = proc(CallerPredId, _CallerProcId) },
		prog_out__write_context(Context),
		io__write_string("Unable to check termination in predicate:\n"),
		prog_out__write_context(Context),
		hlds_out__write_pred_id(Module, PredId),
		( { PredId = CallerPredId } ->
			io__write_string("as it contains a\n")
		;
			io__nl,
			prog_out__write_context(Context),
			io__write_string(
				"as it is in the same SCC as the following predicate\n"
				),
			prog_out__write_context(Context),
			hlds_out__write_pred_id(Module, CallerPredId),
			io__write_string(". That predicate contains a\n")
		),
		prog_out__write_context(Context),
		( { PredId = CalledPredId } ->
			io__write_string("directly recursive call")
		;
			io__write_string("recursive call to"),
			hlds_out__write_pred_id(Module, CalledPredId),
			io__nl,
			prog_out__write_context(Context)
		),
		io__write_string("with the size of the variables increased.\n")
	;
		% only for hlds_dump
		{ CalledPPId = proc(CalledPredId, _CalledProcId) },
		{ CallerPPId = proc(CallerPredId, _CallerProcId) },
		prog_out__write_context(Context),
		io__write_string("this SCC contains a recursive call from "),
		hlds_out__write_pred_id(Module, CallerPredId),
		io__write_string("to "),
		hlds_out__write_pred_id(Module, CalledPredId),
		io__write_string("with the size of the variables increased.\n")
	).
term_errors__output(MaybePredId, Module, Context - horder_call) -->
	prog_out__write_context(Context),
	( { MaybePredId = yes(PredId) } ->
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("horder_call\n").
term_errors__output(MaybePredId, Module, Context - pragma_c_code) -->
	prog_out__write_context(Context),
	( { MaybePredId = yes(PredId) } ->
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("pragma_c_code\n").
term_errors__output(MaybePredId, Module, 
		Context - dont_know_proc_called(PPId)) -->
	{ PPId = proc(CallPredId, _ProcId) },
	( { MaybePredId = yes(PredId) } ->
		prog_out__write_context(Context),
		hlds_out__write_pred_id(Module, PredId),
		io__nl,
		prog_out__write_context(Context)
	;
		[]
	),
	io__write_string("dont_know_proc_called"),
	( { MaybePredId = yes(_) } ->
		io__nl
	;
		[]
	),
	prog_out__write_context(Context),
	hlds_out__write_pred_id(Module, CallPredId),
	io__nl.
term_errors__output(MaybePredId,Module,
		Context - dont_know_proc(_PPId)) -->
	prog_out__write_context(Context),
	( { MaybePredId = yes(PredId) } ->
		hlds_out__write_pred_id(Module, PredId),
		io__nl,
		prog_out__write_context(Context)
	;
		[]
	),
	io__write_string("dont_know_proc\n").
term_errors__output(MaybePredId, Module, Context - horder_args(_PPId)) -->
	prog_out__write_context(Context),
	( { MaybePredId = yes(PredId) } ->
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("horder_args\n").
term_errors__output(MaybePredId, Module, 
		Context - inf_termination_const(PPId)) -->
	{ PPId = proc(CallPredId, _ProcId) },
	( { MaybePredId = yes(PredId) } ->
		prog_out__write_context(Context),
		hlds_out__write_pred_id(Module, PredId),
		io__nl,
		prog_out__write_context(Context),
		io__write_string("inf_termination_const"),
		io__nl
	;
		io__write_string("inf_termination_const")
	),
	prog_out__write_context(Context),
	hlds_out__write_pred_id(Module, CallPredId),
	io__nl.
term_errors__output(MaybePredId, Module, 
		Context - ite_wrong_vars(Vars1, Vars2)) -->
	prog_out__write_context(Context),
	( { MaybePredId = yes(PredId) } ->
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("ite_wrong_vars\nVars1: "),
	term_errors__output_2(Vars1),
	io__write_string("\nVars2: "),
	term_errors__output_2(Vars2).
term_errors__output(MaybePredId, Module, 
		Context - switch_wrong_vars(Vars1, Vars2)) -->
	prog_out__write_context(Context),
	( { MaybePredId = yes(PredId) } ->
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("switch_wrong_vars\nVars1: "),
	term_errors__output_2(Vars1),
	io__write_string("\nVars2: "),
	term_errors__output_2(Vars2).
term_errors__output(MaybePredId, Module, 
		Context - disj_wrong_vars(Vars1, Vars2)) -->
	prog_out__write_context(Context),
	( { MaybePredId = yes(PredId) } ->
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("disj_wrong_vars\nVars1: "),
	term_errors__output_2(Vars1),
	io__write_string("\nVars2: "),
	term_errors__output_2(Vars2).
term_errors__output(MaybePredId, Module, 
		Context - not_subset(Vars1, Vars2)) -->
	( { MaybePredId = yes(PredId) } ->
		prog_out__write_context(Context),
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("not_subset\nCalculated: "),
	term_errors__output_2(Vars1),
	io__write_string("\nDeclared: "),
	term_errors__output_2(Vars2),
	io__nl.
term_errors__output(MaybePredId, Module, Context - not_dag) -->
	( { MaybePredId = yes(PredId) } ->
		prog_out__write_context(Context),
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("not_dag\n").
term_errors__output(MaybePredId, Module, Context - no_eqns) -->
	( { MaybePredId = yes(PredId) } ->
		prog_out__write_context(Context),
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("no_eqns\n").
term_errors__output(MaybePredId, Module, Context - lpsolve_failed(_Reason)) -->
	( { MaybePredId = yes(PredId) } ->
		prog_out__write_context(Context),
		hlds_out__write_pred_id(Module, PredId)
	;
		[]
	),
	io__write_string("lpsolve_failed\n").
term_errors__output(MaybePredId, Module, 
		Context - call_in_single_arg(PPId)) -->
	{ PPId = proc(CallPredId, _ProcId) },
	( { MaybePredId = yes(PredId) } ->
		prog_out__write_context(Context),
		io__write_string("While processing "),
		hlds_out__write_pred_id(Module, PredId),
		io__nl,
		prog_out__write_context(Context),
		io__write_string("single argument analysis encountered a "),
		io__write_string("call that could not be processed\n")
	;
		io__write_string("single argument analysis encountered a "),
		io__write_string("call that could not be processed ")
	),
	prog_out__write_context(Context),
	hlds_out__write_pred_id(Module, CallPredId),
	io__nl.

term_errors__output(MaybePredId, Module, 
		_Context - single_arg_failed(Error)) -->
	io__write_string(
	"Single argument analysis failed to find a head variable that was\n"),
	io__write_string(
	"always decreasing in size.  Normal termination analysis failed \n"),
	io__write_string("for the following reason\n"),
	term_errors__output(MaybePredId, Module, Error).

term_errors__output(MaybePredId, Module, 
		_Context - single_arg_failed(Error1, Error2)) -->
	term_errors__output(MaybePredId, Module, Error1),
	term_errors__output(MaybePredId, Module, Error2).

:- pred term_errors__output_2(bag(var), io__state, io__state).
:- mode term_errors__output_2(in, di, uo) is det.
term_errors__output_2(Vs) -->
	( { bag__remove_smallest(Vs, V, Vs0) } ->
		{ term__var_to_int(V, Num) },
		io__write_int(Num),
		io__write_string(" "),
		term_errors__output_2(Vs0)
	;
		[]
	).	
