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
% identifying the deconstructions in which cell die if the procedure is called
% in the appropriate way. The "appropriate way" is described by a reuse
% condition. 
%
%-----------------------------------------------------------------------------%

:- module structure_reuse__sr_direct.
:- interface.

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module possible_alias__pa_alias_as.

:- import_module io. 

:- pred sr_direct__process_proc(alias_as_table::in, pred_id::in, proc_id::in, 
		proc_info::in, proc_info::out, 
		module_info::in, module_info::out,
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

	% The direct-reuse analysis consists of three steps: 
	% 1. pre-annotations (local forward use, local backward use)
	% 2. 'deadness' analysis, i.e. identifying where datastructures
	% potentially die. 
	% 3. 'choice' analysis, i.e. identify where dead datastructure can be
	% reused. 
process_proc(AliasTable, PredId, ProcId, 
		ProcInfo0, ProcInfo, ModuleInfo0, ModuleInfo) -->
	% Some pre-processing: 
	% - Initialise the reuse information.
	% - Annotate goals with local forward use (lfu).
	% - Annotate goals with local backward use (lbu). 
	% - Annotate the goals with their goal-paths (used to identify the
	% unifications, later in the choice analysis)
	% XXX these goal-paths should become the main way of identifying the
	% places of reuse, instead of annotating the actual goals.
	{ sr_lfu__process_proc(ProcInfo0, ProcInfo1) },
	{ sr_lbu__process_proc(ModuleInfo0, ProcInfo1, ProcInfo2b) },
	{ goal_path__fill_slots(ProcInfo2b, ModuleInfo0, ProcInfo2) }, 

	globals__io_lookup_bool_option(very_verbose, VeryVerbose),

	% After the preliminary annotations, perform the actual analysis of the
	% procedure goal. 
	passes_aux__write_proc_progress_message("% Analysing ", 
			PredId, ProcId, ModuleInfo0), 

	{ proc_info_goal(ProcInfo2, Goal0) },

	% 'Deadness' analysis: determine the deconstructions in which data
	% structures potentially die. 
	passes_aux__maybe_write_string(VeryVerbose, "%\tdeadness analysis..."),
	{ sr_dead__process_goal(PredId, ProcInfo0, ModuleInfo0, 
			AliasTable, Goal0,Goal1) },
	passes_aux__maybe_write_string(VeryVerbose, "done.\n"),

	% 'Choice' analysis: determine how the detected dead data structures
	% can be reused locally. 
	passes_aux__maybe_write_string(VeryVerbose, "%\tchoice analysis..."),
	{ proc_info_vartypes(ProcInfo0, VarTypes) }, 

	% XXX Getting the strategy also performs the check whether the
	% arguments given to the mmc were correct. This is definitely not the
	% right moment to check these arguments. Should be done way earlier. 
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


