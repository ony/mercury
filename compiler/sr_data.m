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
:- import_module set, std_util, list.

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

:- type reuse_var == pair(prog_var, reuse_condition).
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
			set(reuse_var)
		)
	.

	% A reuse, whether direct or indirect, is only allowed as long
	% as the caller fulfills some conditions.  This type keeps track
	% of the information needed to verify whether the condition for
	% reuse is met or not. 
:- type reuse_condition
	--->	always
	;	condition(
		   nodes 		:: set(pa_datastruct__datastruct),
		   local_use_headvars 	:: set(prog_var),
		   local_alias_headvars :: alias_as 
		).

:- pred reuse_condition_merge( reuse_condition::in, 
				reuse_condition::in,
				reuse_condition::out) is det.

:- pred reuse_condition_equal(reuse_condition, reuse_condition).
:- mode reuse_condition_equal(in, in) is semidet.

	% condition_init(Var, LFUi, LBUi, ALIASi, HVs, Condition).
:- pred reuse_condition_init(prog_var, set(prog_var), set(prog_var), 
		alias_as, list(prog_var), reuse_condition).
:- mode reuse_condition_init(in, in, in, in, in, out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module list.
:- import_module pa_datastruct, pa_alias_as.

reuse_condition_merge( C1, C2, C ):-
	(
		reuse_condition_equal( C1, C2 )
	->
		C = C1
	;
		reuse_condition_merge_2( C1, C2, C )
	).

:- pred reuse_condition_merge_2( reuse_condition::in, 
				reuse_condition::in,
				reuse_condition::out ) is det.

reuse_condition_merge_2( C1, C2, C) :- 
	(
		C1 = condition( N1, U1, A1 )
	->
		(
			C2 = condition( N2, U2, A2 )
		->
			set__union( N1, N2, N),
			set__union( U1, U2, U),
			pa_alias_as__add(A1, A2, A),
			C = condition( N, U, A )
		;
			% C2 = always
			C = C1
		)
	;
		% C1 = always
		C = C2
	).
			
			
reuse_condition_equal(always, always).
reuse_condition_equal(condition(NODES1, LU1, LA1), 
			condition(NODES2, LU2, LA2)):-
	set__equal(NODES1, NODES2),
	set__equal(LU1, LU2),
	pa_alias_as__equal(LA1, LA2).

reuse_condition_init(Var, LFUi, LBUi, ALIASi, HVs, CONDITION):- 
	% First determine the nodes to which the reuse is related. 
	% There are two cased:
	% 1. Var is a headvar, then it is sufficient to keep the topcel
	%    of that Var as only node. HeadVar-datastructures aliased
	%    to that node will still be retraceable at the moment 
	%    of verifying the condition
	% 2. Var is a local var, then we must compute all the headvar-
	%    datastructures aliased to the topcel of this var 
	%    (note that the aliases to some substructure of this var are
	%     not relevant for the nodes). All the obtained datastructures
	%    are the nodes for our condition. 
	pa_datastruct__init(Var, TopCel),
	(
		list__member(Var, HVs)
	->
		NODES = [TopCel]
	;
		pa_alias_as__collect_aliases_of_datastruct(TopCel, 
			ALIASi, AliasedData),
		list__filter(
			pred(DATA::in) is semidet :-
			  ( pa_datastruct__get_var(DATA,V), 
			    list__member(V, HVs) ),
			AliasedData,
			NODES)
	),
	(
		NODES = []
	->
		CONDITION = always
	;
		set__union(LFUi, LBUi, LUi),
		set__list_to_set(HVs, HVsSet),
		set__intersect(LUi, HVsSet, LUiHVs),
		pa_alias_as__project( HVs, ALIASi, LAiHVs),
		set__list_to_set(NODES, NODES_set),
		CONDITION = condition(NODES_set,LUiHVs, LAiHVs)
	).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
