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

:- import_module map, list, set, std_util, int.
:- import_module assoc_list.
:- import_module require.

:- import_module sr_lfu, sr_lbu, sr_dead, sr_choice, sr_data, sr_live.
:- import_module hlds_goal, hlds_data, prog_data.

process_proc(PredId, _ProcId, ProcInfo0, ProcInfo, ModuleInfo0, ModuleInfo) -->
		% Determine the LFU (local forward use)
	{ sr_lfu__process_proc(ProcInfo0, ProcInfo1) },

		% Determine the LBU (local backward use)
	{ sr_lbu__process_proc(ModuleInfo0, ProcInfo1, ProcInfo2) },

		% Determine which cells die and can be reused and what
		% the conditions on that reuse are
	{ proc_info_goal(ProcInfo2, Goal0) },

	{ sr_dead__process_goal(PredId,ProcInfo0,ModuleInfo0,Goal0,Goal1) },

		% Select which cells will be reused and which can be
		% compile time garbage collected.
	{ sr_choice__process_goal(strategy(same_cons_id, random),
			Goal1, Goal, _MaybeReuseConditions) },

	{ proc_info_set_goal( ProcInfo2, Goal, ProcInfo ) },
	{ ModuleInfo = ModuleInfo0 }.

