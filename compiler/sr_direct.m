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

:- import_module sr_lfu, sr_lbu, sr_dead, sr_choice.

process_proc(_PredId, _ProcId, ProcInfo0, ProcInfo, ModuleInfo0, ModuleInfo) -->
	% Determine the LFU (local forward use)

	% Determine the LBU (local backward use)

	% Determine which cells die and can be reused and what the
	% conditions on that reuse are

	% Select which cells will be reused and which can be compile
	% time garbage collected.

	{ ProcInfo = ProcInfo0 },
	{ ModuleInfo = ModuleInfo0 }.
	
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
