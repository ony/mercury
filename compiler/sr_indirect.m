%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_indirect
% Main authors: nancy
% 
% Determine the indirect reuse.  This requires a fixpoint computation.
%
%-----------------------------------------------------------------------------%

:- module sr_indirect.
:- interface.

:- import_module hlds_module, io.

:- pred sr_indirect__compute_fixpoint(module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

compute_fixpoint(ModuleInfo0, ModuleInfo) -->
	{ ModuleInfo = ModuleInfo0 }.
	
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
