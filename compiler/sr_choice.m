%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_choice
% Main authors: petdr
% 
% Given a goal annotated with information about which cells are
% canditates for reuse and a strategy determine which cells will
% actually be reused and the conditions that reuse implies on the head
% variables.
%
%-----------------------------------------------------------------------------%

:- module sr_choice.
:- interface.

:- import_module hlds_goal, sr_data.
:- import_module list, std_util.

:- type strategy
	--->	strategy(
			constraint,
			selection
		).

	% The constraint on the cells that we consider available for
	% reuse.
:- type constraint
	--->	same_cons_id
	.

	% After the constraint has been applied to the set of cells
	% which are available for reuse, determine which of that set we
	% select.
:- type selection
	--->	lifo
	.

:- pred sr_choice__process_goal(strategy::in, hlds_goal::in, hlds_goal::out,
		maybe(list(reuse_condition))::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

process_goal(_Strategy, Goal0, Goal, MaybeReuseConditions) :-
	Goal = Goal0,
	MaybeReuseConditions = no.
	
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
