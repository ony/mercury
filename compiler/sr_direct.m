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
:- import_module structure_reuse__sr_choice_util. 
:- import_module structure_reuse__sr_data.

:- import_module io, std_util, list. 

:- pred sr_direct__process_proc(strategy::in, alias_as_table::in, 
		pred_id::in, proc_id::in, 
		proc_info::in, proc_info::out, 
		maybe(list(reuse_condition))::out, 
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
:- import_module structure_reuse__sr_choice_graphing.
:- import_module structure_reuse__sr_dead.
:- import_module structure_reuse__sr_lbu.
:- import_module structure_reuse__sr_lfu.
:- import_module structure_reuse__sr_live.

:- import_module map, list, set, std_util, int, bool, string.
:- import_module assoc_list.
:- import_module require.

	% The direct-reuse analysis consists of three steps: 
	% 1. pre-annotate the analysed goal with lfu and lbu information. 
	% 2. determine where datastructures die, i.e. have a sort of "deadness"
	%  	analyis. 
	% 3. determine how to reuse the detected dead data structures. This is
	% 	the so called "choice analysis". 
	% 
	% XXX 
	% During the choice analysis, program points are identified by the
	% goal-paths leading to thes points. This should become the main way of
	% identifying placed of reuse, instead of annotating the actual goals. 
process_proc(Strategy, AliasTable, PredId, ProcId, 
		!ProcInfo, MaybeReuseConditions1, ModuleInfo, ModuleInfo,
		!IO) :- 
	globals__io_lookup_bool_option(very_verbose, VeryVerbose, !IO),

	sr_lfu__process_proc(!ProcInfo), 
	sr_lbu__process_proc(ModuleInfo, !ProcInfo), 
	goal_path__fill_slots(!.ProcInfo, ModuleInfo, !:ProcInfo),

	passes_aux__write_proc_progress_message("% Analysing ", 
			PredId, ProcId, ModuleInfo, !IO), 

	proc_info_goal(!.ProcInfo, Goal1),

	% 'Deadness' analysis: determine the deconstructions in which data
	% structures potentially die. 
	passes_aux__maybe_write_string(VeryVerbose, 
		"%\tdeadness analysis...", !IO),
	sr_dead__process_goal(PredId, !.ProcInfo, ModuleInfo, 
			AliasTable, DeadCellTable), 
	passes_aux__maybe_write_string(VeryVerbose, "done.\n", !IO),

	% 'Choice' analysis: determine how the detected dead data structures
	% can be reused locally. 
	passes_aux__maybe_write_string(VeryVerbose, 
		"%\tchoice analysis...\n", !IO),
	proc_info_vartypes(!.ProcInfo, VarTypes), 

	sr_choice_graphing__set_background_info(Strategy, 
		ModuleInfo, VarTypes, Background), 
	sr_choice_graphing__process_goal(Background, 
		DeadCellTable, Goal1, Goal,
		MaybeReuseConditions, !IO),
	(
		VeryVerbose = yes 
	->
		(
			MaybeReuseConditions = yes(Cs)
		->
			list__length(Cs, LCs),
			reuse_conditions_simplify(Cs, RCs), 
			list__length(RCs, LRCs), 
			string__int_to_string(LCs, LCS), 
			string__int_to_string(LRCs, LRCS), 
			string__append_list([" done (", LCS, " / ", 
					LRCS, ").\n"], Msg3) , 
			io__write_string(Msg3, !IO)
		; 
			io__write_string("done (no direct reuse).\n", !IO)
		)
	; 
		true
	), 
	
	memo_reuse_simplify(MaybeReuseConditions, MaybeReuseConditions1),
	proc_info_set_goal(!.ProcInfo, Goal, !:ProcInfo).


