%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_data
% Main authors: nancy
% 
% The data structures which are shared between the various phases of the
% structure reuse analysis.
%
%-----------------------------------------------------------------------------%

:- module sr_data.
:- interface.

:- import_module hlds_goal, pa_alias_as, pa_datastruct, prog_data.
:- import_module list, set, std_util.

	% The information placed in the goal info which is used by
	% structure reuse.
	% This field should be initilaised to empty.
	% The sr_dead module replaces empty with choice.
	% The sr_choice module replaces choice with reuse.
:- type reuse_goal_info
	--->	empty
	;	choice(choice_info)
	;	reuse(short_reuse_info)
	.

:- type choice_info
	--->	deconstruct(
				% The condition under which this cell
				% can be reused, if at all.
			maybe(reuse_condition)
		)
	;	construct(
				% The cells which could be reused by the
				% current construction unification and
				% the condition associated with reusing
				% that cell.
			set(pair(prog_var, reuse_condition))
		)
	.

	% A reuse, whether direct or indirect, is only allowed as long
	% as the caller fulfills some conditions.  This type keeps track
	% of the information needed to verify whether the condition for
	% reuse is met or not. 
:- type reuse_condition
	--->	always
	;	condition(
		   nodes 		:: list(pa_datastruct__datastruct),
		   local_use_headvars 	:: set(prog_var),
		   local_alias_headvars :: alias_as 
		).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
