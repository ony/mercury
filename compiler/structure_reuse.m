%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	structure_reuse
% Main authors: nancy, petdr
%
% The top level module for placing structure reuse annotations onto the
% HLDS.
%
% Structure reuse is broken up into two phases: the direct reuse
% analysis (sr_direct) and the indirect analysis (sr_indirect).
% 
% list__append(H1, H2, H3) :-
% 	(
% 		H1 => [],
% 		H3 := H2
% 	;
% 			% Cell H1 dies provided some condition about the
% 			% aliasing of H1 is true.  This is a direct
% 			% reuse.
% 		H1 => [X | Xs],
%
% 			% If the condition about the aliasing of H1
% 			% is true then we can call the version of
% 			% list__append which does reuse.
% 			% This is an indirect reuse.
% 		list__append(Xs, H2, Zs),
%
%			% Reuse the dead cell H1.  This is a direct
%			% reuse.
% 		H3 <= [X | Zs]
% 	).
%
%-----------------------------------------------------------------------------%

:- module structure_reuse.
:- interface.

:- import_module hlds_module.
:- import_module io.

:- pred structure_reuse(module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module passes_aux, sr_direct, sr_indirect.

structure_reuse(HLDS0, HLDS) -->
		% Do the direct reuse analysis phase.
	process_all_nonimported_procs(
			update_module_io(sr_direct__process_proc),
			HLDS0, HLDS1),

		% Do the fixpoint computation to determine all the indirect
		% reuse, and the implied conditions.
	sr_indirect__compute_fixpoint(HLDS1, HLDS).
	
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
