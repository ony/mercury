%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_dead
% Main authors: nancy
% 
% Mark each cell that dies with its reuse_condition, and mark each
% construction with the cells that construction could possibly reuse.
% sr_choice is responsivle for deciding which cell will actually be
% reused.
%
%-----------------------------------------------------------------------------%

:- module sr_dead.
:- interface.

:- import_module hlds_goal.

:- pred sr_dead__process_goal(hlds_goal::in, hlds_goal::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

process_goal(Goal0, Goal) :-
	Goal = Goal0.
	
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
