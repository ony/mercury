%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
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

:- module sr_direct.
:- interface.

:- import_module hlds_module, hlds_pred, io.

:- pred sr_direct__process_proc(pred_id::in, proc_id::in, proc_info::in,
		proc_info::out, module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module map, list, set, std_util, int, bool.
:- import_module assoc_list.
:- import_module require.

:- import_module sr_lfu, sr_lbu, sr_dead, sr_choice, sr_data, sr_live.
:- import_module hlds_goal, hlds_data, prog_data.
:- import_module hlds_pred, passes_aux.
:- import_module globals, options.

process_proc(PredId, ProcId, ProcInfo0, ProcInfo, ModuleInfo0, ModuleInfo) -->
		% Determine the LFU (local forward use)
	globals__io_lookup_bool_option(very_verbose, VeryVerbose),
	{ sr_lfu__process_proc(ProcInfo0, ProcInfo1) },

		% Determine the LBU (local backward use)
	{ sr_lbu__process_proc(ModuleInfo0, ProcInfo1, ProcInfo2) },

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
	{ sr_choice__process_goal(strategy(same_cons_id, random),
			Goal1, Goal, MaybeReuseConditions) },
	maybe_write_string(VeryVerbose, "done.\n"),
	{ proc_info_set_reuse_information( ProcInfo2, MaybeReuseConditions, 
			ProcInfo3 ) },
	{ proc_info_set_goal( ProcInfo3, Goal, ProcInfo ) },
	{ ModuleInfo = ModuleInfo0 }.

