%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% file: profiling.m
% main author: conway

%------------------------------------------------------------------------------%
% This module contains predicates for generating code instrumented for
% `deep' profiling. As well as the information here, more information can
% be found in runtime/mercury_prof_deep.{c,h}.
%
% Deep profiling is a form of profiling which does not make the assumption 
% that all calls to a given predicate have equal cost - an assumption made
% by profilers like prof, gprof, and mprof.  Instead, it records the call
% tree (collapsed into strongly connected components (SCCs)), and
% distinguishes each callsite on an SCC-wise basis.
%
% There are two main kinds of structure associated with the instrumented code:
%	- SCCIds which are structures which describe a static SCC by
%	  enumerating the call sites in the procedures that make up the
%	  SCC. The following information is stored about each call site:
%		- the caller's MR_Stack_Layout_Entry structure
%		- the callee's MR_Stack_Layout_Entry structure
%		- the line number on which the call occurs
%		- whether the call is a first-order, higher-order or
%		  class-method call.
%	- SCCInstances which correspond to a runtime instance of a static
%	  SCC. They contain the following information:
%		- which SCCId it is an instance of
%		- a profile structure for each first order call site at
%		  which a call occured, and a pointer to an SCCInstance for
%		  the callee.
%		- for each higher order call, a list of (closure, profile)
%		  tuples which record a profile for each different
%		  procedure that is called from this site.
%		- for each class method call, a list of (closure, profile)
%		  tuples which record a profile for each different
%		  procedure that is called from this site.
%		- a list of (closure, profile) structures for each
%		  different call back into mercury from C that occured from
%		  inside this SCC.
%
% We don't store an SCCInstance for leaf procedures, since the profile
% structure is stored in the caller's SCCInstance and therefore there
% can be no call-sites in it.
%
%------------------------------------------------------------------------------%
:- module profiling.

:- interface.

:- import_module code_info, hlds_module, hlds_pred, llds.
:- import_module list, std_util, term.

		% Compute the call graph, number the SCCs and create
		% the mapping from pred_proc_id to SCC-number.
:- pred profiling__compute_scc_info(module_info, module_info).
:- mode profiling__compute_scc_info(in, out) is det.

		% Allocate a pair of stack-slots for storing the
		% MR_prof_current_proc variable.
:- pred profiling__setup(code_info, code_info).
:- mode profiling__setup(in, out) is det.

		% Generate the code fragment that goes in the prologue
		% which saves MR_prof_current_{proc,scc} on to the stack
		% and increments the number of calls.
:- pred profiling__prologue(code_tree, code_info, code_info).
:- mode profiling__prologue(out, in, out) is det.

		% Generate the code fragment the for the epilogue for
		% when a procedure succeeds.
:- pred profiling__success_epilogue(code_tree, code_info, code_info).
:- mode profiling__success_epilogue(out, in, out) is det.

		% Generate the code fragment the for the epilogue for
		% when a procedure fails.
:- pred profiling__failure_epilogue(code_tree, code_info, code_info).
:- mode profiling__failure_epilogue(out, in, out) is det.

		% Generate the code framgent to update the deep profiling
		% pointers before a first order call.
:- pred profiling__pre_call_update(pred_proc_id, term__context, code_tree,
		code_info, code_info).
:- mode profiling__pre_call_update(in, in, out, in, out) is det.

		% Generate the code framgent to update the deep profiling
		% pointers after a call.
:- pred profiling__post_call_update(code_tree, code_info, code_info).
:- mode profiling__post_call_update(out, in, out) is det.

		% Generate the code framgent to update the deep profiling
		% pointers before a higher order call.
:- pred profiling__pre_ho_call_update(rval, term__context, code_tree,
		code_info, code_info).
:- mode profiling__pre_ho_call_update(in, in, out, in, out) is det.

		% Generate the code framgent to update the deep profiling
		% pointers after an higher-order call.
:- pred profiling__post_ho_call_update(code_tree, code_info, code_info).
:- mode profiling__post_ho_call_update(out, in, out) is det.

		% Generate the code framgent to update the deep profiling
		% pointers when forward execution resumes.
:- pred profiling__resume_code(code_tree, code_info, code_info).
:- mode profiling__resume_code(out, in, out) is det.

		% Generate the MR_SCCId structures for a module.
:- pred profiling__generate_scc_ids(module_info, module_info,
		list(comp_gen_c_data), list(comp_gen_c_var)).
:- mode profiling__generate_scc_ids(in, out, out, out) is det.

		% Find the MR_SCCId for a given procedure.
:- pred profiling__scc_id(pred_proc_id, maybe(rval), code_info, code_info).
:- mode profiling__scc_id(in, out, in, out) is det.

%------------------------------------------------------------------------------%

:- implementation.

:- import_module code_util, dependency_graph, goal_util, llds_out, tree.
:- import_module continuation_info.
:- import_module goal_util, hlds_data, hlds_goal, prog_data, globals, options.
:- import_module bool, int, map, std_util, string, term.

profiling__compute_scc_info(ModuleInfo0, ModuleInfo) :-
	module_info_globals(ModuleInfo0, Globals),
	globals__lookup_bool_option(Globals, profile_deep, ProfileDetail),
	( ProfileDetail = yes ->
		module_info_clobber_dependency_info(ModuleInfo0, ModuleInfo0a),
		module_info_ensure_dependency_info(ModuleInfo0a, ModuleInfo1),
		module_info_dependency_info(ModuleInfo1, DepInfo),
		hlds_dependency_info_get_dependency_ordering(DepInfo, Ordering),
		map__init(SCCMembers0),
		map__init(SCCData0),
		compute_scc_members(Ordering, 0, ModuleInfo1, SCCMembers0,
			SCCMembers, SCCData0, SCCData),
		SCCInfo = scc_info(SCCMembers, SCCData),
		module_info_set_scc_info(ModuleInfo1, SCCInfo, ModuleInfo)
	;
		ModuleInfo = ModuleInfo0
	).

%------------------------------------------------------------------------------%

:- pred compute_scc_members(list(list(pred_proc_id)), int, module_info,
		map(pred_proc_id, scc_id), map(pred_proc_id, scc_id),
		map(scc_id, scc_data), map(scc_id, scc_data)).
:- mode compute_scc_members(in, in, in, in, out, in, out) is det.

compute_scc_members([], _N, _ModuleInfo, Members, Members, Data, Data).
compute_scc_members([SCC|SCCs], N0, ModuleInfo, Members0, Members,
		Data0, Data) :-
	module_info_name(ModuleInfo, Name),
	compute_scc_members1(SCC, scc_id(Name, N0), ModuleInfo, Members0,
		Members1, Data0, Data1),
	N1 is N0 + 1,
	compute_scc_members(SCCs, N1, ModuleInfo, Members1, Members,
		Data1, Data).

:- pred compute_scc_members1(list(pred_proc_id), scc_id, module_info,
		map(pred_proc_id, scc_id), map(pred_proc_id, scc_id),
		map(scc_id, scc_data), map(scc_id, scc_data)).
:- mode compute_scc_members1(in, in, in, in, out, in, out) is det.

compute_scc_members1([], _SCCId, _ModuleInfo, Members, Members, Data, Data).
compute_scc_members1([PPId|PPIds], SCCId, ModuleInfo, Members0, Members,
		Data0, Data) :-
	(
		% Figure out if this PPId belongs to a procedure in this
		% module, and it is not a leaf procedure then we need to
		% allocate a SCC data-structure for it.
		proc_needs_scc(PPId, ModuleInfo, MayCallMercury)
	->
		map__det_insert(Members0, PPId, SCCId, Members1),
		( MayCallMercury = may_call_mercury ->
			map__set(Data0, SCCId, scc_data(0, [], 0, [], 0, [],
				MayCallMercury), Data1)
		;
			Data1 = Data0
		)
	;
		Members1 = Members0,
		Data1 = Data0
	),
	compute_scc_members1(PPIds, SCCId, ModuleInfo, Members1, Members,
		Data1, Data).

:- pred proc_needs_scc(pred_proc_id, module_info, may_call_mercury).
:- mode proc_needs_scc(in, in, out) is semidet.

proc_needs_scc(PPId, ModuleInfo, MayCallMercury) :-
	proc_has_local_code(PPId, ModuleInfo),
	PPId = proc(PredId, ProcId),
	module_info_pred_proc_info(ModuleInfo, PredId, ProcId, _Pred, Proc),
	proc_info_goal(Proc, Goal),
	proc_needs_scc_2(Goal, yes, IsALeaf,
		will_not_call_mercury, MayCallMercury),
	IsALeaf = no.

:- pred proc_needs_scc_2(hlds_goal, bool, bool,
		may_call_mercury, may_call_mercury).
:- mode proc_needs_scc_2(in, in, out, in, out) is det.

proc_needs_scc_2(Goal - _GoalInfo, IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury) :-
	proc_needs_scc_3(Goal, IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury).

:- pred proc_needs_scc_3(hlds_goal_expr, bool, bool,
		may_call_mercury, may_call_mercury).
:- mode proc_needs_scc_3(in, in, out, in, out) is det.

proc_needs_scc_3(conj(Goals), IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury) :-
	foldl2(proc_needs_scc_2, Goals, IsALeaf0, IsALeaf, MayCallMercury0,
		MayCallMercury).

proc_needs_scc_3(par_conj(Goals, _), IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury) :-
	foldl2(proc_needs_scc_2, Goals, IsALeaf0, IsALeaf, MayCallMercury0,
		MayCallMercury).

proc_needs_scc_3(disj(Goals, _), IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury) :-
	foldl2(proc_needs_scc_2, Goals, IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury).

proc_needs_scc_3(switch(_, _, Cases, _), IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury) :-
	foldl2((pred(case(_, Goal)::in, L0::in, L::out, M0::in, M::out)
			is det :-
		proc_needs_scc_2(Goal, L0, L, M0, M)
	), Cases, IsALeaf0, IsALeaf, MayCallMercury0, MayCallMercury).

proc_needs_scc_3(call(_, _, _, Builtin, _, _), IsALeaf0, IsALeaf,
		MayCallMercury, MayCallMercury) :-
	( Builtin \= inline_builtin ->
		IsALeaf = no
	;
		IsALeaf = IsALeaf0
	).

proc_needs_scc_3(generic_call(_, _, _, _), _, no,
		MayCallMercury, MayCallMercury).

proc_needs_scc_3(unify(_, _, _, _, _), IsALeaf, IsALeaf,
		MayCallMercury, MayCallMercury).

proc_needs_scc_3(not(Goal), IsALeaf0, IsALeaf, MayCallMercury0, MayCallMercury) :-
	proc_needs_scc_2(Goal, IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury).

proc_needs_scc_3(some(_, _, Goal), IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury) :-
	proc_needs_scc_2(Goal, IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury).

proc_needs_scc_3(bi_implication(GoalA, GoalB), IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury) :-
	proc_needs_scc_2(GoalA, IsALeaf0, IsALeaf1,
		MayCallMercury0, MayCallMercury1),
	proc_needs_scc_2(GoalB, IsALeaf1, IsALeaf,
		MayCallMercury1, MayCallMercury).

proc_needs_scc_3(if_then_else(_, C, T, E, _), IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury) :-
	foldl2(proc_needs_scc_2, [C, T, E], IsALeaf0, IsALeaf,
		MayCallMercury0, MayCallMercury).

proc_needs_scc_3(pragma_c_code(Attrs, _, _, _, _, _, _), IsALeaf, IsALeaf,
		MayCallMercury0, MayCallMercury) :-
	( may_call_mercury(Attrs, may_call_mercury) ->
		MayCallMercury = may_call_mercury
	;
		MayCallMercury = MayCallMercury0
	).

:- pred proc_has_local_code(pred_proc_id, module_info).
:- mode proc_has_local_code(in, in) is semidet.

proc_has_local_code(PPId, ModuleInfo) :-
	PPId = proc(PredId, ProcId),
	module_info_pred_proc_info(ModuleInfo, PredId, ProcId, Pred, _Proc),
	pred_info_import_status(Pred, ImportStatus),
	(
		status_defined_in_this_module(ImportStatus, yes)
	;
		% if the ImportStatus is pseudo_imported then we do need
		% an SCC entry because we generate code for this procedure
		ImportStatus = pseudo_imported
	).

%------------------------------------------------------------------------------%

profiling__setup -->
	code_info__acquire_temp_slot(profiling_data, ProcSlot),
	code_info__get_scc_info(SCCInfo),
	{ SCCInfo = scc_info(ProcSCCs, _) },
	profiling__my_ppid(MyPPId),
	(
		% If this procedure has an scc structure associated with
		% it, then we need to allocate a stack slot to store its
		% cycle-check value, and we construct its scc_id rval once.
		{ search(ProcSCCs, MyPPId, scc_id(ModuleName, SCCNum)) }
	->
		{ MySCCId = const(data_addr_const(data_addr(ModuleName,
			scc_id(SCCNum)))) },
		code_info__acquire_temp_slot(profiling_data, CounterSlot),
		{ MCycleStuff = yes(cycle_stuff(MySCCId, CounterSlot)) }
	;
		{ MCycleStuff = no }
	),
	{ PI = deep_profiling_info(ProcSlot, MCycleStuff) },
	code_info__set_deep_profiling_info(PI).

	%
	% In the prologue, we save the current SCCInstance onto the stack,
	% and also a pointer to the current CallProfile structure.
	% Also, in the prologue we increment the number of calls to
	% this procedure.
	%
profiling__prologue(Code) -->
	code_info__get_deep_profiling_info(PI),
	{ PI = deep_profiling_info(ProcSlot, MCycleStuff) },
	{ CurProc = global(data_ptr, "MR_prof_current_proc") },
	( { MCycleStuff = yes(CycleStuff) } ->
		{ MySCCId = CycleStuff^mySCCId },
		{ CounterSlot = CycleStuff^saveSlot },
		{ Inst = c_func(data_ptr, "MR_SCC_INST",
				[data_ptr - MySCCId], static) },
		{ SCCCode = node([
			assign(CounterSlot, Inst) - "",
			c_code("MR_scc_from_here($1);\n",
				[MySCCId]) - "update the current SCCInstance"
		]) }
	;
		{ SCCCode = empty }
	),
	{ BasicCode = node([
		assign(ProcSlot, lval(CurProc)) - "",
		c_code("MR_prof_current_proc->calls++;\n", []) - ""
	]) },
	{ Code = tree(SCCCode, BasicCode) }.

	%
	% We generate two epilogues: one for success and one for failure.
	% Each updates the appropriate counter in the current_proc structure.
	%
profiling__success_epilogue(SuccCode) -->
	code_info__get_deep_profiling_info(PI),
	{ PI = deep_profiling_info(_ProcSlot, MCycleStuff) },
	( { MCycleStuff = yes(CycleStuff) } ->
		{ MySCCId = CycleStuff^mySCCId },
		{ CounterSlot = CycleStuff^saveSlot },
		{ RestoreCode = node([
			c_code("MR_SET_SCC_INST($1, $2);",
				[MySCCId, lval(CounterSlot)]) - ""
		]) }
	;
		{ RestoreCode = empty }
	),
	{ SuccCode = tree(node([
		c_code("MR_prof_current_proc->successes++;\n", []) -
			"update the profiling information"
	]), RestoreCode) }.

profiling__failure_epilogue(FailCode) -->
	code_info__get_deep_profiling_info(PI),
	{ PI = deep_profiling_info(_ProcSlot, MCycleStuff) },
	( { MCycleStuff = yes(CycleStuff) } ->
		{ MySCCId = CycleStuff^mySCCId },
		{ CounterSlot = CycleStuff^saveSlot },
		{ RestoreCode = node([
			c_code("MR_SET_SCC_INST($1, $2);",
				[MySCCId, lval(CounterSlot)]) - ""
		]) }
	;
		{ RestoreCode = empty }
	),
	{ FailCode = tree(node([
		c_code("MR_prof_current_proc->failures++;\n", []) -
			"update the profiling information"
	]), RestoreCode) }.

%------------------------------------------------------------------------------%

	%
	% Before a (first order) call there are three situations
	%	- the call is an intra-module, intra-scc call, in which case
	%	  we assign the address of the appropriate CallProfile
	%	  structure to the global current_call_profile variable,
	%	  allocating the structure if it didn't already exist.
	%	- the call is an intra-module, inter-scc call, in which case
	%	  we do the same as above, and assign to the global
	%	  current_scc variable the address of the child SCCInstance
	%	  structure, allocating it if necessary. (We distinguish
	%	  this case from the next - for inter-module calls because
	%	  for intra-module inter-scc calls we know at compile time
	%	  the SCCId for the called procedure, so we can do a
	%	  direct assignment rather than having to refer to it
	%	  via it's proc_layout structure.
	%	- the call is an inter-module, inter-scc call (all inter-
	%	  module calls are assumed to be inter-scc calls), in which
	%	  case we do the same as above, except that the SCCId must
	%	  be obtained indirectly through the proc_layout structures.
	%
profiling__pre_call_update(CalleePPId, Context, Code) -->
	profiling__my_ppid(CallerPPId),
	{ ThisSite = first_order_call(CallerPPId, CalleePPId, Context) },
	profiling__add_callsite(fo(ThisSite), _UpdateFunc, CallSiteNum),
	code_info__get_deep_profiling_info(PI),
	{ PI = deep_profiling_info(_ProcSlot, _MCounterSlot) },
	{ CProc = global(data_ptr, "MR_prof_current_proc") },
	code_info__get_module_info(ModuleInfo),
	code_info__get_scc_info(SCCInfo0),
	{ SCCInfo0 = scc_info(ProcSCCs, _SCCCallSites) },
	{ map__lookup(ProcSCCs, CallerPPId, CallerSCC) },
	(
			% Check to see if the callee is in the
			% same SCC as the caller.
		{ map__search(ProcSCCs, CalleePPId, CalleeSCC0) },
		{ CalleeSCC0 = CallerSCC }
	->
		{ Code = node([
			assign(CProc, c_func(data_ptr, "MR_intra_scc_call",
				[word - const(int_const(CallSiteNum))],
				dynamic)) - "update the current CallProf"
		]) }
	;
			% Check to see if we know which SCC the callee
			% is in. Leaf procedures are not allocated an
			% SCC number, because we don't need a whole SCC
			% structure for them.
		{ map__search(ProcSCCs, CalleePPId, CalleeSCC1) }
		% { CalleeSCC1 \= CallerSCC }
	->
		{ CalleeSCC1 = scc_id(ModuleName, SCCNum) },
		{ ChildSCCId = const(data_addr_const(data_addr(ModuleName,
			scc_id(SCCNum)))) },
		{ Code = node([
			assign(CProc, c_func(data_ptr, "MR_local_inter_scc",
				[word - const(int_const(CallSiteNum)),
				data_ptr - ChildSCCId], dynamic)) -
					"update the current CallProf"
		]) }
	;
			% The callee is a leaf procedure, so we don't want it's
			% SCCId. We pass NULL instead, which the runtime
			% recognises appropriately.
		{ pred_has_local_code(CalleePPId, ModuleInfo) }
	->
		{ Code = node([
			assign(CProc, c_func(data_ptr, "MR_local_inter_scc",
				[word - const(int_const(CallSiteNum)),
				data_ptr - const(int_const(0))], dynamic)) -
					"update the current CallProf"
		]) }
	;
			% The callee is in another module (or compilation
			% unit), so we need to pass the proc_id layout
			% structure to the runtime so it can create the new
			% SCC instance.
		{ CalleePPId = proc(Pred, Proc) },
		{ code_util__make_proc_label(ModuleInfo, Pred, Proc, ProcLab) },
		{ ProcEntry = proc_layout(local(ProcLab)) },
		{ pred_module(CalleePPId, ModuleInfo, ModuleName) },
		{ ChildProcLayout = const(data_addr_const(data_addr(ModuleName,
			ProcEntry))) },
		{ Code = node([
			assign(CProc, c_func(data_ptr, "MR_nonlocal_inter_scc",
				[word - const(int_const(CallSiteNum)),
				data_ptr - ChildProcLayout], dynamic)) -
					"update the current CallProf"
		]) }
	).

profiling__post_call_update(Code) -->
	code_info__get_deep_profiling_info(PI),
	{ PI = deep_profiling_info(ProcSlot, _MCounterSlot) },
	{ Code = node([
		assign(global(data_ptr, "MR_prof_current_proc"), lval(ProcSlot))
			- ""
	]) }.

profiling__pre_ho_call_update(Closure, Context, Code) -->
	profiling__my_ppid(CallerPPId),
	{ ThisSite = higher_order_call(CallerPPId, Context) },
	profiling__add_callsite(ho(ThisSite), UpdateFunc, CallSiteNum),
	code_info__get_deep_profiling_info(PI),
	{ PI = deep_profiling_info(_ProcSlot, _MCounterSlot) },
	{ CProc = global(data_ptr, "MR_prof_current_proc") },
	{ Code = node([
		assign(CProc, c_func(data_ptr, UpdateFunc,
			[word - const(int_const(CallSiteNum)),
			word - Closure], dynamic)) -
				"update the current CallProf"
	]) }.

profiling__post_ho_call_update(Code) -->
	code_info__get_deep_profiling_info(PI),
	{ PI = deep_profiling_info(ProcSlot, _MCounterSlot) },
	{ Code = node([
		assign(global(data_ptr, "MR_prof_current_proc"), lval(ProcSlot))
			- ""
	]) }.

profiling__resume_code(Code) -->
	code_info__get_deep_profiling_info(PI),
	{ PI = deep_profiling_info(ProcSlot, _MCycleStuff) },
	{ Code = node([
		assign(global(data_ptr, "MR_prof_current_proc"), lval(ProcSlot))
			- ""
	]) }.

%------------------------------------------------------------------------------%

:- pred profiling__my_ppid(pred_proc_id, code_info, code_info).
:- mode profiling__my_ppid(out, in, out) is det.

profiling__my_ppid(PPId) -->
	code_info__get_pred_id(CallerPredId),
	code_info__get_proc_id(CallerProcId),
	{ PPId = proc(CallerPredId, CallerProcId) }.

%------------------------------------------------------------------------------%

:- type callsite
	--->	fo(first_order_call)
	;	ho(higher_order_call)
	;	cm(class_method_call)
	.

:- pred profiling__add_callsite(callsite, string, int, code_info, code_info).
:- mode profiling__add_callsite(in, out, out, in, out) is det.

profiling__add_callsite(CallSite, UpdateFunc, SlotNum) -->
	profiling__my_ppid(CallerPPId),
	code_info__get_scc_info(SCCInfo0),
	{ SCCInfo0 = scc_info(ProcSCCs, SCCCallSites0) },
	{ map__lookup(ProcSCCs, CallerPPId, CallerSCC) },
	( { map__search(SCCCallSites0, CallerSCC, SCCData0a) } ->
		{ SCCData0 = SCCData0a }
	;
		{ SCCData0 = scc_data(0, [], 0, [], 0, [],
			will_not_call_mercury) }
	),
	{ SCCData0 = scc_data(A0, As0, B0, Bs0, C0, Cs0, Rec) },
	(
		{ CallSite = fo(ThisSite) },
		{ A is A0 + 1 },
		{ list__append(As0, [ThisSite], As) },
		{ UpdateFunc = "MR_fo_call" },
		{ B = B0, Bs = Bs0 },
		{ C = C0, Cs = Cs0 },
		{ SlotNum = A0 }
	;
		{ CallSite = ho(ThisSite) },
		{ B is B0 + 1 },
		{ list__append(Bs0, [ThisSite], Bs) },
		{ UpdateFunc = "MR_ho_call" },
		{ A = A0, As = As0 },
		{ C = C0, Cs = Cs0 },
		{ SlotNum = B0 }
	;
		{ CallSite = cm(ThisSite) },
		{ C is C0 + 1 },
		{ list__append(Cs0, [ThisSite], Cs) },
		{ UpdateFunc = "MR_cm_call" },
		{ A = A0, As = As0 },
		{ B = B0, Bs = Bs0 },
		{ SlotNum = C0 }
	),
	{ SCCData = scc_data(A, As, B, Bs, C, Cs, Rec) },
	{ map__set(SCCCallSites0, CallerSCC, SCCData, SCCCallSites) },
	{ SCCInfo = scc_info(ProcSCCs, SCCCallSites) },
	code_info__set_scc_info(SCCInfo).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- type scc_id_data
	--->	scc_id_data(int, list(comp_gen_c_data), list(comp_gen_c_var)).

profiling__generate_scc_ids(ModuleInfo0, ModuleInfo, Data, Vars) :-
	module_info_get_scc_info(ModuleInfo0, SCCInfo),
	module_info_get_cell_count(ModuleInfo0, InitialCount),
	SCCInfo = scc_info(_ProcSCCs, SCCCallSites),
	InitialSCCIdData = scc_id_data(InitialCount, [], []),
	map__foldl(lambda([SCCId::in, SCCData::in,
			SCCIdData0::in, SCCIdData8::out] is det, (
		SCCId = scc_id(ModuleName, SCCNum),
		SCCData = scc_data(NFO, FOCalls, NHO, HOCalls, NCM, CMCalls,
				_Rec),
		(
			FOCalls = [],
			FOVector = yes(const(int_const(0))),
			SCCIdData2 = SCCIdData0
		;
			FOCalls = [_|_],
			list__map_foldl(first_order_scc_ids(ModuleInfo0),
				FOCalls, FOCallRvals, SCCIdData0, SCCIdData1),
			profiling__scc_id_data_next_cell(LabNum1, SCCIdData1,
				SCCIdData2),
			FOVector = yes(create(0, FOCallRvals, uniform(no),
				must_be_static,
				LabNum1, "first order call data", no))
		),
		(
			HOCalls = [],
			HOVector = yes(const(int_const(0))),
			SCCIdData2 = SCCIdData4
		;
			HOCalls = [_|_],
			list__map_foldl(higher_order_scc_ids(ModuleInfo0),
				HOCalls, HOCallRvals, SCCIdData2, SCCIdData3),
			profiling__scc_id_data_next_cell(LabNum2, SCCIdData3,
				SCCIdData4),
			HOVector = yes(create(0, HOCallRvals, uniform(no),
				must_be_static,
				LabNum2, "higher order call data", no))
		),
		(
			CMCalls = [],
			CMVector = yes(const(int_const(0))),
			SCCIdData6 = SCCIdData4
		;
			CMCalls = [_|_],
			list__map_foldl(class_method_scc_ids(ModuleInfo0),
				CMCalls, CMCallRvals, SCCIdData4, SCCIdData5),
			profiling__scc_id_data_next_cell(LabNum3, SCCIdData5,
				SCCIdData6),
			CMVector = yes(create(0, CMCallRvals, uniform(no),
				must_be_static,
				LabNum3, "class method data", no))
		),
		scc_id_data_next_cell(LabNum4, SCCIdData6, SCCIdData7),
		CYCCHK = yes(create(0, [
			yes(const(int_const(0)))
		], uniform(no), must_be_dynamic, LabNum4, "", no)),
		MRVals = [
			yes(const(int_const(NFO))),
			FOVector,
			yes(const(int_const(NHO))),
			HOVector,
			yes(const(int_const(NCM))),
			CMVector,
			CYCCHK
		],
		CData = comp_gen_c_data(ModuleName, scc_id(SCCNum), yes,
				MRVals, uniform(no), []),
		SCCIdData7 = scc_id_data(Count, CDataList0, CVarsList0),
		GlobData = scc_id_counter(ModuleName, SCCNum),
		CDataList = [CData|CDataList0],
		CVarsList = [GlobData|CVarsList0],
		SCCIdData8 = scc_id_data(Count, CDataList, CVarsList)
	)), SCCCallSites, InitialSCCIdData, FinalSCCIdData),
	FinalSCCIdData = scc_id_data(FinalCount, Data, Vars),
	module_info_set_cell_count(ModuleInfo0, FinalCount, ModuleInfo).

%------------------------------------------------------------------------------%

:- pred first_order_scc_ids(module_info, first_order_call, maybe(rval),
		scc_id_data, scc_id_data).
:- mode first_order_scc_ids(in, in, out, in, out) is det.

first_order_scc_ids(ModuleInfo, FOCall, MRval) -->
	{ FOCall = first_order_call(CallerPPId, CalleePPId, Context) },
	{ code_util__make_proc_layout_ref(CallerPPId, ModuleInfo,
		CallerLayout) },
	{ code_util__make_proc_layout_ref(CalleePPId, ModuleInfo,
		CalleeLayout) },
	profiling__scc_id_data_next_cell(CellNum),
	{ term__context_file(Context, File) },
	{ term__context_line(Context, Line) },
	{ MRval = yes(create(0, [
		yes(CallerLayout),
		yes(CalleeLayout),
		yes(const(string_const(File))),
		yes(const(int_const(Line)))
	], uniform(no), must_be_static, CellNum, "fo_call_site", no)) }.

%------------------------------------------------------------------------------%

:- pred higher_order_scc_ids(module_info, higher_order_call, maybe(rval),
		scc_id_data, scc_id_data).
:- mode higher_order_scc_ids(in, in, out, in, out) is det.

higher_order_scc_ids(ModuleInfo, HOCall, MRval) -->
	{ HOCall = higher_order_call(CallerPPId, Context) },
	{ code_util__make_proc_layout_ref(CallerPPId, ModuleInfo,
		CallerLayout) },
	profiling__scc_id_data_next_cell(CellNum),
	{ term__context_file(Context, File) },
	{ term__context_line(Context, Line) },
	{ MRval = yes(create(0, [
		yes(CallerLayout),
		yes(const(int_const(0))),
		yes(const(string_const(File))),
		yes(const(int_const(Line)))
	], uniform(no), must_be_static, CellNum, "ho_call_site", no)) }.

%------------------------------------------------------------------------------%

:- pred class_method_scc_ids(module_info, class_method_call, maybe(rval),
		scc_id_data, scc_id_data).
:- mode class_method_scc_ids(in, in, out, in, out) is det.

class_method_scc_ids(ModuleInfo, CMCall, MRval) -->
	{ CMCall = class_method_call(CallerPPId, CalleePPId, Context) },
	{ code_util__make_proc_layout_ref(CallerPPId, ModuleInfo,
		CallerLayout) },
	{ code_util__make_proc_layout_ref(CalleePPId, ModuleInfo,
		CalleeLayout) },
	profiling__scc_id_data_next_cell(CellNum),
	{ term__context_file(Context, File) },
	{ term__context_line(Context, Line) },
	{ MRval = yes(create(0, [
		yes(CallerLayout),
		yes(CalleeLayout),
		yes(const(string_const(File))),
		yes(const(int_const(Line)))
	], uniform(no), must_be_static, CellNum, "cm_call_site", no)) }.

%------------------------------------------------------------------------------%

:- pred profiling__scc_id_data_next_cell(int, scc_id_data, scc_id_data).
:- mode profiling__scc_id_data_next_cell(out, in, out) is det.

profiling__scc_id_data_next_cell(Cell, Data0, Data) :-
	Data0 = scc_id_data(Cell, Structs, Vars),
	Cell1 is Cell + 1,
	Data = scc_id_data(Cell1, Structs, Vars).

%------------------------------------------------------------------------------%

profiling__scc_id(PredProcId, MSCCIdRval) -->
	code_info__get_globals(Globals),
	{ globals__lookup_bool_option(Globals, profile_deep, DeepProfiling) },
	(
		{ DeepProfiling = no },
		{ MSCCIdRval = no }
	;
		{ DeepProfiling = yes },
		code_info__get_scc_info(scc_info(SCCIds, _)),
		code_info__get_module_info(ModuleInfo),
		( { map__search(SCCIds, PredProcId, SCCId) } ->
			{ SCCId = scc_id(ModuleName, SCCNum) },
			{ SCCIdRval = const(data_addr_const(
				data_addr(ModuleName, scc_id(SCCNum)))) },
			{ MSCCIdRval = yes(SCCIdRval) }
		; { not proc_has_local_code(PredProcId, ModuleInfo) } ->
				% If the procedure is defined in another
				% module, then we create a tagged pointer
				% to the MR_Stack_Layout_Entry structure
				% (which must exist in this grade).
				%
				% This is necessary for the case in which
				% we take the address of a non-leaf
				% procedure that is defined in another
				% module. In that case, we don't know its
				% SCCId, and can't figure it out directly.
			{ PredProcId = proc(PredId, ProcId) },
			{ code_util__make_local_entry_label(ModuleInfo,
				PredId, ProcId, no, EntryLabel) },
			{ module_info_name(ModuleInfo, ModuleName) },
			{ SCCIdRval = mkword(1, const(data_addr_const(
				data_addr(ModuleName,
				proc_layout(EntryLabel))))) },
			{ MSCCIdRval = yes(SCCIdRval) }
		;
			{ MSCCIdRval = yes(const(int_const(0))) }
		)
	).

