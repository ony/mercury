%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_direct
% Main authors: nancy, petdr
% 
% Determine the direct reuse in one procedure.  Direct reuse consists of
% identifying which cells die.
%
%-----------------------------------------------------------------------------%

:- module structure_reuse__sr_direct.
:- interface.

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.

:- import_module io. 

:- pred sr_direct__process_proc(pred_id::in, proc_id::in, proc_info::in,
		proc_info::out, module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.


:- import_module check_hlds__goal_path.
:- import_module hlds__hlds_data.
:- import_module hlds__hlds_goal.
:- import_module hlds__passes_aux.
:- import_module libs__globals.
:- import_module libs__options.
:- import_module parse_tree__prog_data.
:- import_module structure_reuse__sr_choice. 
:- import_module structure_reuse__sr_choice_graphing.
:- import_module structure_reuse__sr_choice_util. 
:- import_module structure_reuse__sr_data.
:- import_module structure_reuse__sr_dead.
:- import_module structure_reuse__sr_lbu.
:- import_module structure_reuse__sr_lfu.
:- import_module structure_reuse__sr_live.

:- import_module map, list, set, std_util, int, bool, string.
:- import_module assoc_list.
:- import_module require.

process_proc(PredId, ProcId, ProcInfo0, ProcInfo, ModuleInfo0, ModuleInfo) -->
		% Determine the LFU (local forward use)
	globals__io_lookup_bool_option(very_verbose, VeryVerbose),
	{ initialise_reuse_info(ProcInfo0, ProcInfo00) },
	{ sr_lfu__process_proc(ProcInfo00, ProcInfo1) },

		% Determine the LBU (local backward use)
	{ sr_lbu__process_proc(ModuleInfo0, ProcInfo1, ProcInfo2b) },

		% Annotate the goals with their goal-paths.
	{ goal_path__fill_slots(ProcInfo2b, ModuleInfo0, ProcInfo2) }, 

		% Determine which cells die and can be reused and what
		% the conditions on that reuse are
	{ proc_info_goal(ProcInfo2, Goal0) },

	(
		{ VeryVerbose = yes }
	->
		passes_aux__write_proc_progress_message(
			"% Analysing ", PredId, ProcId, ModuleInfo0), 
		io__write_string("%\tdeadness analysis...")
	; 
		[]
	),
	{ sr_dead__process_goal(PredId,ProcInfo0,ModuleInfo0,Goal0,Goal1) },

	maybe_write_string(VeryVerbose, "done.\n"),

		% Select which cells will be reused and which can be
		% compile time garbage collected.
	maybe_write_string(VeryVerbose, "%\tchoice analysis..."),
	% sr_choice__get_strategy(Strategy, ModuleInfo0, ModuleInfo),
	% { proc_info_vartypes(ProcInfo0, VarTypes) },
	% { sr_choice__process_goal(Strategy, VarTypes, ModuleInfo,
	%		ProcInfo0, Goal1, Goal, MaybeReuseConditions) },
	{ proc_info_vartypes(ProcInfo0, VarTypes) }, 
	% { ModuleInfo = ModuleInfo0 }, 
	sr_choice_util__get_strategy(Strategy, ModuleInfo0, ModuleInfo),
	{ Strategy = strategy(Constraint, Selection) },
	(
		{ Selection = graph }
	->
		{ sr_choice_graphing__set_background_info(Constraint, 
			ModuleInfo, VarTypes, Background) }, 
		sr_choice_graphing__process_goal(Background, Goal1, Goal,
			MaybeReuseConditions)
	;
		{ sr_choice__process_goal(Strategy, VarTypes, ModuleInfo, 
			ProcInfo0, Goal1, Goal, MaybeReuseConditions) }
	),
	(
		{ VeryVerbose = yes } 
	->
		(
			{ MaybeReuseConditions = yes(Cs) }
		->
			{ list__length(Cs, LCs) },
			{ reuse_conditions_simplify(Cs, RCs) }, 
			{ list__length(RCs, LRCs) }, 
			{ string__int_to_string(LCs, LCS)}, 
			{ string__int_to_string(LRCs, LRCS) }, 
			{ string__append_list([" done (", LCS, " / ", 
					LRCS, ").\n"], Msg3) }, 
			io__write_string(Msg3)
		; 
			io__write_string("done (no direct reuse).\n")
		)
	; 
		[]
	), 
	
	{ memo_reuse_simplify(MaybeReuseConditions, MaybeReuseConditions1) },
	{ proc_info_set_reuse_information(ProcInfo2, MaybeReuseConditions1, 
			ProcInfo3) },
	{ proc_info_set_goal(ProcInfo3, Goal, ProcInfo) }.


:- pred initialise_reuse_info(proc_info::in, proc_info::out) is det.

initialise_reuse_info(ProcInfo0, ProcInfo) :- 
	proc_info_goal(ProcInfo0, Goal0), 
	initialise_reuse_info_in_goal(Goal0, Goal),
	proc_info_set_goal(ProcInfo0, Goal, ProcInfo).

:- pred initialise_reuse_info_in_goal(hlds_goal::in, hlds_goal::out) is det.

initialise_reuse_info_in_goal(Expr0 - Info0, Expr - Info) :- 
	goal_info_reuse_init(Info0, Info),
	initialise_reuse_info_in_subgoal(Expr0, Expr). 

:- pred initialise_reuse_info_in_subgoal(hlds_goal_expr::in, 
		hlds_goal_expr::out) is det.

initialise_reuse_info_in_subgoal(conj(Goals0), conj(Goals)):- 
	list__map(initialise_reuse_info_in_goal, Goals0, Goals).
initialise_reuse_info_in_subgoal(call(A,B,C,D,E,F), call(A,B,C,D,E,F)).
initialise_reuse_info_in_subgoal(generic_call(A,B,C,D), generic_call(A,B,C,D)).
initialise_reuse_info_in_subgoal(switch(A,B,Cases0),switch(A,B,Cases)) :-
	list__map(
		pred(Case0::in, Case::out) is det :- 
			( Case0 = case(C,G0), 
			initialise_reuse_info_in_goal(G0,G),
			Case = case(C,G)), Cases0, Cases).
initialise_reuse_info_in_subgoal(unify(A,B,C,D,E), unify(A,B,C,D,E)).
initialise_reuse_info_in_subgoal(disj(Goals0), disj(Goals)):- 
	list__map(initialise_reuse_info_in_goal, Goals0, Goals).
initialise_reuse_info_in_subgoal(not(Goal0), not(Goal)):- 
	initialise_reuse_info_in_goal(Goal0, Goal).
initialise_reuse_info_in_subgoal(some(A,B,G0),some(A,B,G)):- 
	initialise_reuse_info_in_goal(G0, G).
initialise_reuse_info_in_subgoal(if_then_else(A,I0,T0,E0),
		if_then_else(A,I,T,E)):- 
	initialise_reuse_info_in_goal(I0, I),
	initialise_reuse_info_in_goal(T0, T),
	initialise_reuse_info_in_goal(E0, E).
initialise_reuse_info_in_subgoal(foreign_proc(A,B,C,D,E,F,G),
		foreign_proc(A,B,C,D,E,F,G)).
initialise_reuse_info_in_subgoal(par_conj(G),par_conj(G)).
initialise_reuse_info_in_subgoal(shorthand(G),shorthand(G)).

