%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_run: implements the process of annotating each procedure
%		 with possible alias information. The analysis is
%		 goal-independent, and thus returns only those aliases that
%		 are created by the analysed procedure, without taking into
%		 account the possible aliases that might exist when calling
%		 that procedure. (cf. Phd Nancy, chapter 6). 
% main author: nancy

:- module possible_alias__pa_run.

:- interface.

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module parse_tree__prog_data.
:- import_module possible_alias__pa_alias_as.

:- import_module io, list.

	% the main pass
:- pred pa_run__aliases_pass(module_info::in, module_info::out, 
		io__state::di, io__state::uo) is det.

	% Write the pa_info pragma for the given pred_id (if that
	% pred_id does not belong to the list(pred_id). 
	% 
	% XXX The result of the analysis should be possible alias information
	% written as a publicly available type within the HLDS. The predicate
	% for actually writing out the pragma should be moved to somewhere (?)
	% else. Note that this predicate is used in "trans_opt", while the
	% "public" types will probably be defined in prog_data.
:- pred pa_run__write_pred_pa_info(module_info::in, list(pred_id)::in, 
		pred_id::in, io__state::di, io__state::uo) is det.

	% Lookup the alias-information for some pred_id proc_id in the
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
	%		ActualTypes = types of the args with which the
	% 			proc is called
	%		AliasIN = alias at moment of call
	%		AliasOUT = alias at end of call
	% 
	% XXX While the result of the possible alias pass should be expressed
	% in a "public" type for outputting the HLDS and alike, yet it is
	% preferrable to keep the optimised representation as well for its
	% use during the structure reuse pass.  This is a bit of a dilemma.
:- pred pa_run__extend_with_call_alias(module_info::in, proc_info::in, 
		pred_id::in, proc_id::in, list(prog_var)::in, 
		list((type))::in, alias_as::in, alias_as::out) is det. 

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
:- implementation.

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_pred.
:- import_module hlds__instmap.
:- import_module hlds__passes_aux.
:- import_module hlds__special_pred.
:- import_module libs__globals.
:- import_module libs__options.
:- import_module ll_backend__liveness.
:- import_module parse_tree__mercury_to_mercury.
:- import_module parse_tree__modules.
:- import_module parse_tree__prog_data.
:- import_module parse_tree__prog_out.
:- import_module parse_tree__prog_util.
:- import_module possible_alias__pa_alias_as.
:- import_module possible_alias__pa_prelim_run.
:- import_module possible_alias__pa_sr_util.
:- import_module possible_alias__pa_util.
	% may 20, 2004: should not be necessary
% :- import_module structure_reuse__sr_lbu.
% :- import_module structure_reuse__sr_lfu.
:- import_module transform_hlds__dependency_graph.

:- import_module require.
:- import_module list, map, int, set.
:- import_module std_util, string.
:- import_module term.
:- import_module varset, bool.

%-----------------------------------------------------------------------------%

pa_run__aliases_pass(HLDSin, HLDSout) -->
	% preliminary steps:

	% 0. process all the alias-information for all the imported 
	% predicates.
	pa_prelim_run__process_imported_predicates(HLDSin, HLDS0),

	% 1. annotate all the liveness
	pa_prelim_run__annotate_all_liveness_in_module(HLDS0, HLDS1),

	% 2. annotate all the outscope vars
	{ pa_prelim_run__annotate_all_outscope_vars_in_module(HLDS1,HLDS2) },

	% 3. and finally do the actual aliases pass
	aliases_pass_2(HLDS2, HLDSout).

:- pred aliases_pass_2(module_info, module_info, io__state, io__state).
:- mode aliases_pass_2(in, out, di, uo) is det.

pa_run__aliases_pass_2(HLDSin, HLDSout) -->
		% strongly connected components needed
	{ module_info_ensure_dependency_info(HLDSin, HLDS1) },
	{ module_info_get_maybe_dependency_info(HLDS1, MaybeDepInfo) } ,
	(
		{ MaybeDepInfo = yes(DepInfo) }
	->
		{ hlds_dependency_info_get_dependency_ordering(DepInfo, DepOrdering) },
		% perform the analysis, and annotate the procedures
		run_with_dependencies(DepOrdering, HLDS1, HLDSout) %,
		% write out the results of the exported procedures into
		% a separate interface-file. 
		% pa_run__make_pa_interface(HLDSout)
	;
		{ error("(pa) pa_run module: no dependency info") }
	).

:- pred run_with_dependencies(dependency_ordering, module_info, 
					module_info, io__state, io__state).
:- mode run_with_dependencies(in, in, out, di, uo) is det.

run_with_dependencies(Deps, HLDSin, HLDSout) -->
	list__foldl2(run_with_dependency, Deps, HLDSin, HLDSout).

:- pred run_with_dependency(list(pred_proc_id), module_info, module_info,
				io__state, io__state).
:- mode run_with_dependency(in, in, out, di, uo) is det.

run_with_dependency(SCC , HLDSin, HLDSout) -->
	(
		% analysis ignores special predicates
		{ pa_sr_util__some_are_special_preds(SCC, HLDSin) }
	->
		{ HLDSout = HLDSin }
	;
		% for each list of strongly connected components, 
		% perform a fixpoint computation.
		{ pa_util__pa_fixpoint_table_init(SCC, FPtable0) } , 
		run_with_dependency_until_fixpoint(SCC, FPtable0, 
					HLDSin, HLDSout)
	).

:- pred run_with_dependency_until_fixpoint(list(pred_proc_id), 
		pa_util__pa_fixpoint_table, module_info, module_info,
		io__state, io__state).
:- mode run_with_dependency_until_fixpoint(in, in, in, out, di, uo) is det.

run_with_dependency_until_fixpoint(SCC, FPtable0, HLDSin, HLDSout) -->
	list__foldl2(analyse_pred_proc(HLDSin), SCC, FPtable0, FPtable),
	(
		{ pa_fixpoint_table_all_stable(FPtable) }
	->
		{ list__foldl(update_alias_in_module_info(FPtable), SCC, HLDSin, HLDSout) }
	;
		{ pa_util__pa_fixpoint_table_new_run(FPtable,FPtable1) },
		run_with_dependency_until_fixpoint(SCC, FPtable1, 
				HLDSin, HLDSout)
	).

%-----------------------------------------------------------------------------%
% THE KERNEL 
%-----------------------------------------------------------------------------%
:- pred analyse_pred_proc(module_info, pred_proc_id, pa_fixpoint_table, 
				pa_fixpoint_table, io__state, io__state).
:- mode analyse_pred_proc(in, in, in, out, di, uo) is det.

analyse_pred_proc(HLDS, PRED_PROC_ID , FPtable0, FPtable) -->
	globals__io_lookup_bool_option(very_verbose,Verbose),
	globals__io_lookup_int_option(possible_alias_widening, WideningLimit),

	{ module_info_pred_proc_info(HLDS, PRED_PROC_ID, PredInfo,
			ProcInfo_tmp) },

	% XXX annotate all lbu/lfu stuff
	% may 20, 2004: should not be necessary
	% { sr_lfu__process_proc(ProcInfo_tmp, ProcInfo_tmp2) }, 
	% { sr_lbu__process_proc(HLDS, ProcInfo_tmp2, ProcInfo) }, 

	{ ProcInfo = ProcInfo_tmp }, 

	{ PRED_PROC_ID = proc(PredId, ProcId) },

	{ pa_util__pa_fixpoint_table_which_run(FPtable0, Run) },
	{
	( 
		pa_util__pa_fixpoint_table_get_final_as_semidet(PRED_PROC_ID, 
				TabledAliasAs, FPtable0) 
	->
		TabledSize = size(TabledAliasAs)
	;
		TabledSize = 0
	)
	},
	{ string__int_to_string(Run, SRun)},
	{ string__append_list(["% Alias analysing (run ",SRun,") "],
				Msg) },
	passes_aux__write_proc_progress_message(Msg, 
				PredId, ProcId, HLDS), 

	{ 
		% begin non-io
	proc_info_goal(ProcInfo, Goal), 
	proc_info_headvars(ProcInfo, HeadVars),

	pa_alias_as__init(Alias0)

	},

	(
		{ predict_bottom_aliases(HLDS, ProcInfo) }
	->
		maybe_write_string(Verbose, "% bottom predicted"),
		{ Alias1 = Alias0 }, % = bottom 
		{ FPtable1 = FPtable0 }
	; 
		analyse_goal(ProcInfo, PredInfo, HLDS, Goal, 
			FPtable0, FPtable1, Alias0, Alias1) 
	),

	{ 
	FullSize = pa_alias_as__size(Alias1), 

	pa_alias_as__project(HeadVars, Alias1, Alias2),
	ProjectSize = pa_alias_as__size(Alias2),

	Goal = _ - GoalInfo,
	goal_info_get_instmap_delta(GoalInfo, InstMapDelta),
	instmap__init_reachable(InitIM),
	instmap__apply_instmap_delta(InitIM, InstMapDelta, InstMap),
	pa_alias_as__normalize(HLDS, ProcInfo, InstMap, Alias2, Alias3),
	NormSize = pa_alias_as__size(Alias3),

	pa_alias_as__apply_widening(HLDS, ProcInfo, WideningLimit, 
			Alias3, Alias, Widening),
		
	pa_fixpoint_table_new_as(HLDS, ProcInfo, 
				PRED_PROC_ID, Alias, FPtable1, FPtable)
	 	% end non-io 
 	}, 
	(
		{ Verbose = yes } 
	->
		%	print_maybe_possible_aliases(yes(Alias),ProcInfo), 
		%	io__write_string("\n")
		% []
		{
			( pa_fixpoint_table_all_stable(FPtable) ->
				Stable = "s" ; Stable = "u"
			),
			string__int_to_string(TabledSize, TabledS), 
			string__int_to_string(FullSize, FullS), 
			string__int_to_string(ProjectSize, ProjectS),
			string__int_to_string(NormSize, NormS)
		},
		io__write_strings(["\t\t: ", TabledS, "->", 
					FullS, "/", ProjectS, "/",
					NormS,
					"(", Stable, ")"]), 
		(
			{ Widening = bool__yes }
		-> 
			{ string__int_to_string(
				pa_alias_as__size(Alias), WidenS) }, 
			{ string__int_to_string(WideningLimit, WidLimitS) },
			io__write_strings(["/-->widening(", WidLimitS,"): ", WidenS, "\n"])
		;
			io__write_string("\n")
		)
/**
		,	
		(
			{ dummy_test(PRED_PROC_ID) }
		-> 
			{ dummy_test_here(Alias) },
			io__write_string("Alias = "), 
			pa_alias_as__print_aliases(Alias, ProcInfo,PredInfo),
			io__write_string("\n\n")
		;
			[]
		)
**/

	;
		[]
	).

:- pred predict_bottom_aliases(module_info::in, proc_info::in) is semidet.

predict_bottom_aliases(ModuleInfo, ProcInfo):- 
	proc_info_headvars(ProcInfo, HeadVars), 
	proc_info_argmodes(ProcInfo, Modes), 
	proc_info_vartypes(ProcInfo, VarTypes), 
	list__map( map__lookup(VarTypes), HeadVars, Types), 
	pa_alias_as__predict_bottom_alias(ModuleInfo, HeadVars, Modes, Types).

:- pred dummy_test(pred_proc_id::in) is semidet. 
dummy_test(proc(PredId, _)):- pred_id_to_int(PredId, 16). 
:- pred dummy_test_here(alias_as::in) is det.
dummy_test_here(_). 

	% analyse a given goal, with module_info and fixpoint table
	% to lookup extra information, starting from an initial abstract
	% substitution, and creating a new one. During this process,
	% the fixpoint table might change (when recursive predicates are
	% encountered).
	% analyse_goal(ProcInfo, HLDS, Goal, TableIn, TableOut,
	%		AliasIn, AliasOut).
:- pred analyse_goal(proc_info::in, pred_info::in, module_info::in, 
		hlds_goal::in, pa_fixpoint_table::in, pa_fixpoint_table::out,
		alias_as::in, alias_as::out, 
		io__state::di, io__state::uo) is det.

analyse_goal(ProcInfo, PredInfo, HLDS, Goal, FPtable0, FPtable, 
		Alias0, Alias, !IO) :- 
	Goal = GoalExpr - GoalInfo, 
	analyse_goal_expr(GoalExpr, GoalInfo, ProcInfo, PredInfo, HLDS, 
		FPtable0, FPtable, Alias0, Alias, !IO).
/***
	% extra: after the analysis of the current goal, 
	% project the obtained alias-set (Alias1) to the set 
	% LFUi + LBUi + HeadVars
	(
		% projecting is too expensive to be done for each goal, 
		% let's do it only on non-atomic goals: 
		goal_is_atomic(GoalExpr)
	->
		Alias = Alias1	% projection operation is not worthwhile
	; 
		pa_alias_as__project_on_live_vars(ProcInfo, GoalInfo, 
				Alias1, Alias) 
	).
***/

	
:- pred analyse_goal_expr(hlds_goal_expr::in, hlds_goal_info::in, 
		proc_info::in, pred_info::in, module_info::in, 
		pa_fixpoint_table::in, pa_fixpoint_table::out,
		alias_as::in, alias_as::out, 
		io__state::di, io__state::uo) is det.

analyse_goal_expr(conj(Goals), _Info, ProcInfo, PredInfo, 
		HLDS , !Table, !Alias, !IO) :- 
	list__foldl3(analyse_goal(ProcInfo, PredInfo, HLDS),  Goals, 
		!Table, !Alias, !IO). 

analyse_goal_expr(call(PredId, ProcId, ARGS, _,_, _PName), _Info, 
		ProcInfo, _PredInfo, HLDS, !Table, !Alias, !IO) :- 
% 	write_proc_progress_message("\n--> Call to ", 
%			PredId, ProcId, HLDS, !IO),
	PredProcId = proc(PredId, ProcId),
	lookup_call_alias(PredProcId, HLDS, !Table, CallAlias),
%	module_info_pred_info(HLDS, PredId, PredInfoLookedUp),
%	io__write_string("--> Looked up aliases: ", !IO), 
%	io__write_strings(["(size = ", int_to_string(size(CallAlias)), 
%			") "], !IO),
%	print_brief_aliases(5, CallAlias, ProcInfo, PredInfoLookedUp, !IO),
%	io__write_string("\n--> Existing aliases: ", !IO),
%	io__write_strings(["(size = ", int_to_string(size(!.Alias)), 
%			") "], !IO),
%	print_brief_aliases(5, !.Alias, ProcInfo, PredInfo, !IO),
	
	proc_info_vartypes(ProcInfo, VarTypes), 
	list__map(map__lookup(VarTypes), ARGS, ActualTypes),
	rename_call_alias(PredProcId, HLDS, ARGS, ActualTypes, 
				CallAlias, RenamedCallAlias),
	pa_alias_as__extend(HLDS, ProcInfo, RenamedCallAlias, !Alias).
%	io__write_string("\n--> Extended aliases: ", !IO),
%	io__write_strings(["(size = ", int_to_string(size(!.Alias)), 
%			") "],!IO),
%	print_brief_aliases(5, !.Alias, ProcInfo, PredInfo, !IO).

analyse_goal_expr(generic_call(GenCall,_,_,_), Info, 
		_ProcInfo, _P, _HLDS , !Table, !Alias, !IO) :-
	(
		GenCall = higher_order(_, _, _),
		Text = "higher_order"
	; 
		GenCall = class_method(_, _, _, _),
		Text = "class_method"
	; 
		GenCall = aditi_builtin(_,_),
		Text = "aditi_builtin"
	), 
	goal_info_get_context(Info, Context), 
	term__context_line(Context, ContextLine), 
	term__context_file(Context, ContextFile), 
	string__int_to_string(ContextLine, ContextLineS), 
	string__append_list(["generic_call:",Text," (",ContextFile, ":", 
				ContextLineS, ")"], Msg), 
	pa_alias_as__top(Msg, !Alias). 
	% error("(pa) generic_call not handled") .

analyse_goal_expr(switch(_Var,_CF,Cases), Info, 
		ProcInfo, PredInfo, HLDS, !Table, !Alias, !IO) :- 
	list__map_foldl2(analyse_case(ProcInfo, PredInfo, HLDS, !.Alias), 
				Cases, SwitchAliases, !Table, !IO),
	pa_alias_as__least_upper_bound_list(HLDS, ProcInfo, Info, 
				SwitchAliases, !:Alias).

:- pred analyse_case(proc_info::in, pred_info::in, module_info::in, 
		alias_as::in, case::in, alias_as::out, 
		pa_fixpoint_table::in, pa_fixpoint_table::out, 
		io__state::di, io__state::uo) is det.

analyse_case(ProcInfo, PredInfo, HLDS, Alias0, Case, Alias, !Table, !IO) :-
	Case = case(_, Goal),
	analyse_goal(ProcInfo, PredInfo, HLDS, Goal, 
		!Table, Alias0, Alias, !IO).

analyse_goal_expr(unify(_,_,_,Unification,_), Info, ProcInfo, _PredInfo, 
		HLDS, !Table, !Alias, !IO) :- 
	% io__write_string("\n--> Unification.", !IO),
	% io__write_string("\n--> Existing aliases: ", !IO),
	% io__write_strings(["(size = ", int_to_string(size(A0)), 
			% ") "], !IO),
	% io__write_string("\n", !IO),
	% print_aliases(A0, ProcInfo, PredInfo, !IO),
	pa_alias_as__extend_unification(HLDS, ProcInfo, 
		Unification, Info, !Alias). 
	% io__write_string("\n--> Extended aliases: ", !IO),
	% io__write_strings(["(size = ", int_to_string(size(A)), 
			% ") "], !IO),
	% print_aliases(A, ProcInfo, PredInfo, !IO).

analyse_goal_expr(disj(Goals), Info, ProcInfo, PredInfo, HLDS, 
		!Table, !Alias, !IO) :-
%	io__write_string("\n--> Disjunction", !IO),
	list__map_foldl2(
		pred(Goal::in, Alias::out, FPT0::in, FPT::out, 
			IO0::di, IO::uo) is det :- 
			(analyse_goal(ProcInfo, PredInfo, HLDS, Goal, 
					FPT0, FPT, !.Alias, Alias, IO0, IO)),
		Goals,
		DisjAliases,
		!Table, !IO), 
%	io__write_string("\n-->Disjunction, lub."),
%	list__foldl(
%		pred(AA::in, IO0::di, IO::uo) is det :-
%			( io__write_string("\n--> --> Branch.", IO0, IO1),
%			io__write_strings(["(size = ", 
%					int_to_string(size(AA)), 
%				") "], IO1, IO2),
%			io__write_string("\n", IO2, IO3),
%			print_aliases(AA, ProcInfo, PredInfo, IO3, IO) ),
%			DisjAliases),
	pa_alias_as__least_upper_bound_list(HLDS, ProcInfo, Info, 
		DisjAliases, !:Alias).
%	io__write_string("\n--> LUB"),
%	io__write_strings(["(size = ", int_to_string(size(A)), 
%			") "]),
%	io__write_string("\n"),
%	print_aliases(A, ProcInfo, PredInfo).

analyse_goal_expr(not(Goal), _Info, ProcInfo, PredInfo, 
		HLDS, !Table, !Alias, !IO) :- 
	analyse_goal(ProcInfo, PredInfo, HLDS, Goal, !Table, !Alias, !IO). 

analyse_goal_expr(some(Vars,_,Goal), _Info, ProcInfo, PredInfo, 
		HLDS, !Table, !Alias, !IO) :- 
	(
		Vars = []
	->
		% XXX
		analyse_goal(ProcInfo, PredInfo, HLDS, Goal, 
			!Table, !Alias, !IO) 
	;
		Msg = "(pa_run) analyse_goal_expr: empty vars expected.",
		require__error(Msg)
	).
	% pa_alias_as__top("some not handled", A).
	% error("(pa) some goal not handled") .

analyse_goal_expr(if_then_else(_VARS, IF, THEN, ELSE), _Info, 
		ProcInfo, PredInfo, HLDS, !Table, A0, A, !IO) :- 
	analyse_goal(ProcInfo, PredInfo, HLDS, IF, !Table, A0, A1, !IO),
	analyse_goal(ProcInfo, PredInfo, HLDS, THEN, !Table, A1, A2, !IO),
	analyse_goal(ProcInfo, PredInfo, HLDS, ELSE, !Table, A0, A3, !IO),
	pa_alias_as__least_upper_bound(HLDS, ProcInfo, A2, A3, A).

analyse_goal_expr(foreign_proc(Attrs, PredId, ProcId, 
			Vars, MaybeModes, Types, _), 
		Info, ProcInfo, _PredInfo, HLDS, !Table, !Alias, !IO) :- 
	extend_foreign_code(HLDS, ProcInfo, Attrs, PredId, ProcId, 
			Vars, MaybeModes, Types, Info, !Alias).

analyse_goal_expr(par_conj(_Goals), Info, _, _ , _, !Table, !Alias, !IO) :- 
	goal_info_get_context(Info, Context), 
	term__context_line(Context, ContextLine), 
	term__context_file(Context, ContextFile), 
	string__int_to_string(ContextLine, ContextLineS), 
	string__append_list(["par_conj:",
				" (",ContextFile, ":", 
				ContextLineS, ")"], Msg), 
	pa_alias_as__top(Msg, !Alias).

analyse_goal_expr(shorthand(_), _, _,  _, _, !T, !A, !IO) :- 
	error("pa_run__analyse_goal_expr: shorthand goal").

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
:- pred lookup_call_alias(pred_proc_id, module_info, pa_fixpoint_table,
				pa_fixpoint_table, alias_as).
:- mode lookup_call_alias(in, in, in, out, out) is det.

lookup_call_alias(PRED_PROC_ID, HLDS, FPtable0, FPtable, Alias) :-
	(
		% 1 - check in table
		pa_fixpoint_table_get_as(PRED_PROC_ID, Alias1, 
					FPtable0, FPtable1)
	->
		FPtable = FPtable1,
		Alias   = Alias1
	;
		% 2 - look up in module_info
		lookup_call_alias_in_module_info(HLDS, PRED_PROC_ID, 
				Alias), 
		FPtable = FPtable0
	).

	% exported predicate
extend_with_call_alias(HLDS, ProcInfo, 
		PRED_ID, PROC_ID, ARGS, ActualTypes, ALIASin, ALIASout):-
	PRED_PROC_ID = proc(PRED_ID, PROC_ID), 
	lookup_call_alias_in_module_info(HLDS, PRED_PROC_ID, ALIAS_tmp), 
	rename_call_alias(PRED_PROC_ID, HLDS, ARGS, ActualTypes, 
				ALIAS_tmp, ALIAS_call),
	pa_alias_as__extend(HLDS, ProcInfo, ALIAS_call, ALIASin, ALIASout). 
	
:- pred lookup_call_alias_in_module_info(module_info, pred_proc_id, 
		alias_as). 
:- mode lookup_call_alias_in_module_info(in, in, out) is det.

lookup_call_alias_in_module_info(HLDS, PRED_PROC_ID, Alias) :- 
	module_info_pred_proc_info(HLDS, PRED_PROC_ID, PredInfo,
				    ProcInfo),
	(
		% If the determinism of the called procedure is
		% erroneous or failure, then you don't even need to
		% check anything else anymore: it simply cannot 
		% introduce any aliases. 
		proc_info_inferred_determinism(ProcInfo, Determinism), 
		(
			Determinism = erroneous
		; 
			Determinism = failure
		)
	->
		init(Alias)	
	;
		proc_info_possible_aliases(ProcInfo, MaybeAliases),
		MaybeAliases = yes(SomeAL)
	->
		Alias = SomeAL
	;
		% Special tricks: 
		% 1. check whether the args are primitive types
		arg_types_are_all_primitive(HLDS, PredInfo)
	->
		init(Alias)
	;
		% 2. call to builtin.m or private_builtin.m
		%    predicate -- unify/index/compare
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
		% 3. XXX Any call to private_builtin.m module and
		%        builtin module are considered alias-free. 
		% This is unsafe and it would be much better to 
		% even annotate their aliases manually then just considering
		% them as non-alias by default. 
		pred_info_module(PredInfo, ModuleName),
		(
			mercury_private_builtin_module(ModuleName)
		; 
			mercury_public_builtin_module(ModuleName)
		)
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


%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
% easy stuff

	% once the abstract alias substitution is computed for
	% a procedure, one must simply update the proc-information
	% of that procedure.
:- pred update_alias_in_module_info(pa_util__pa_fixpoint_table, 
					pred_proc_id, module_info,
					module_info).
:- mode update_alias_in_module_info(in, in, in, out) is det.

update_alias_in_module_info(FPtable, PRED_PROC_ID, HLDSin, HLDSout) :-
	module_info_pred_proc_info(HLDSin, PRED_PROC_ID, PredInfo, ProcInfo),
	pa_fixpoint_table_get_final_as(PRED_PROC_ID, ALIAS_AS, FPtable),
	proc_info_set_possible_aliases(ProcInfo, ALIAS_AS, NewProcInfo),
	module_info_set_pred_proc_info(HLDSin, PRED_PROC_ID, PredInfo,
					NewProcInfo, HLDSout).


%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
% make the interface

	% inspiration taken from termination.m
:- pred pa_run__make_pa_interface(module_info, io__state, io__state).
:- mode pa_run__make_pa_interface(in, di, uo) is det.

pa_run__make_pa_interface(HLDS) --> 
	{ module_info_name(HLDS, ModuleName) },
	modules__module_name_to_file_name(ModuleName, ".opt.pa", bool__no, KaFileName),
	globals__io_lookup_bool_option(verbose, Verbose),
	maybe_write_string(Verbose, "% -> writing possible aliases to `"),
	maybe_write_string(Verbose, KaFileName),
	maybe_write_string(Verbose, "'..."),
	maybe_flush_output(Verbose),

	io__open_output(KaFileName, KaFileRes),
	(
		{ KaFileRes = ok(KaFile) },
		io__set_output_stream(KaFile, OldStream),
		pa_run__make_pa_interface_2(HLDS), 
		io__set_output_stream(OldStream, _),
		io__close_output(KaFile),
		maybe_write_string(Verbose, " done.\n"),
		maybe_flush_output(Verbose)
	;
		{ KaFileRes = error(IOError) },
		maybe_write_string(Verbose, " failed!\n"),
		maybe_flush_output(Verbose),
		{ io__error_message(IOError, IOErrorMsg) },
		io__write_strings(["Error opening file `",
                        KaFileName, "' for output: ", IOErrorMsg]),
		io__set_exit_status(1)
       ).

:- pred pa_run__make_pa_interface_2(module_info, 
					io__state, io__state).
:- mode pa_run__make_pa_interface_2(in, di, uo) is det.

pa_run__make_pa_interface_2(HLDS) -->
	{ module_info_name(HLDS, ModuleName) },
	{ module_info_predids(HLDS, PredIds) },
	{ module_info_get_special_pred_map(HLDS, MAP) },
	{ map__values(MAP, SpecPredIds) },
	io__write_string(":- module "),
	mercury_output_sym_name(ModuleName), 
	io__write_string(".\n\n"),
	io__write_string(":- interface. \n"),
	list__foldl(make_pa_interface_pred(HLDS, SpecPredIds), PredIds).

pa_run__write_pred_pa_info(HLDS, SpecPredIds, PredId) -->
	pa_run__make_pa_interface_pred(HLDS, SpecPredIds, PredId).

:- pred pa_run__make_pa_interface_pred(module_info, list(pred_id),pred_id, 
					io__state, io__state).
:- mode pa_run__make_pa_interface_pred(in, in, in, di ,uo) is det.

pa_run__make_pa_interface_pred(HLDS, SpecPredIds, PredId) -->
	{ module_info_pred_info(HLDS, PredId, PredInfo) },
	(
		{ pred_info_import_status(PredInfo, Status), 
		  ( Status = exported ; Status = opt_exported ) }
		  % pred_info_is_exported(PredInfo) ;
		  % pred_info_is_opt_exported(PredInfo) }
	->
		(
			{ list__member(PredId, SpecPredIds) }
		->
			[]
		;
			{ pred_info_procids(PredInfo, ProcIds) },
			{ pred_info_procedures(PredInfo, ProcTable) },
			list__foldl(make_pa_interface_pred_proc(PredInfo,
				    ProcTable),
					ProcIds)
		)
	;
		[]
	).

:- pred pa_run__make_pa_interface_pred_proc(pred_info, proc_table, 
		proc_id, io__state, io__state).
:- mode pa_run__make_pa_interface_pred_proc(in, in, in, di, uo) is det.

pa_run__make_pa_interface_pred_proc(PredInfo, ProcTable, ProcId) -->
	io__write_string(":- pragma possible_alias("),

		% write a simple predicate declaration

	{ varset__init(InitVarSet) },
	{ pred_info_name(PredInfo, PredName) },
	{ pred_info_get_is_pred_or_func(PredInfo, PredOrFunc) },
	{ pred_info_module(PredInfo, ModuleName) },
	{ pred_info_context(PredInfo, Context) },
	{ SymName = qualified(ModuleName, PredName) },

	{ map__lookup(ProcTable, ProcId, ProcInfo) },
	{ proc_info_declared_argmodes(ProcInfo, Modes) },

	(
		{ PredOrFunc = predicate },
		mercury_output_pred_mode_subdecl(InitVarSet, SymName, Modes,
			std_util__no, Context)
	;
		{ PredOrFunc = function },
		{ pred_args_to_func_args(Modes, FuncModes, RetMode) },
		mercury_output_func_mode_subdecl(InitVarSet, SymName, 
			FuncModes, RetMode, std_util__no, Context)
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

		% write alias information

	{ proc_info_possible_aliases(ProcInfo, MaybeAliases) },
	pa_alias_as__print_maybe_interface_aliases(MaybeAliases, 
					ProcInfo, PredInfo),

	io__write_string(").\n").

