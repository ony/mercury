%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module sr_live: implements the datastructure representing the live
%		  set of datastructures, where `live' is to be seen
%		  in the context of the structure reuse analysis.
% main author: nancy

:- module structure_reuse__sr_live.

:- interface.

:- import_module hlds__hlds_module. 
:- import_module hlds__hlds_pred.
:- import_module parse_tree__prog_data.
:- import_module possible_alias__pa_datastruct.

:- import_module set.
:- import_module list.

%-------------------------------------------------------------------%
%-- exported types

:- type live_set.

%-------------------------------------------------------------------%
%-- exported predicates

:- pred init(live_set).
:- mode init(out) is det.

:- pred init(set(prog_var),live_set).
:- mode init(in,out) is det.

:- pred from_datastructs(list(pa_datastruct__datastruct), live_set).
:- mode from_datastructs(in, out) is det.

:- pred bottom(live_set).
:- mode bottom(out) is det.
:- mode bottom(in) is semidet.

:- pred top(live_set).
:- mode top(out) is det.
:- mode top(in) is semidet.

:- pred get_datastructs(live_set, list(pa_datastruct__datastruct)).
:- mode get_datastructs(in, out) is det.

:- pred union(list(live_set), live_set).
:- mode union(in, out) is det.

:- pred is_live(prog_var,live_set).
:- mode is_live(in, in) is semidet.

:- pred is_live_datastruct(module_info, proc_info, 
			pa_datastruct__datastruct, live_set).
:- mode is_live_datastruct(in, in, in, in) is semidet.

:- pred project(list(prog_var), live_set, live_set).
:- mode project(in, in, out) is det.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
:- implementation.

:- import_module require.

%-------------------------------------------------------------------%
%-- additional types 

:- type live_set ---> 
			bottom
		; 	top
		; 	live(list(pa_datastruct__datastruct)).


%-------------------------------------------------------------------%
%-- predicates

init(bottom).
init(VARS, LIVE) :- 
	LiveSet = set__map(
			func_datastruct_init,
			VARS),
	set__to_sorted_list(LiveSet,LiveList),
	live_wrap(LiveList, LIVE).	

from_datastructs(DATASTRUCTS, LIVE) :- 
	% check whether minimal !! 
	live_wrap(DATASTRUCTS, LIVE).

:- func func_datastruct_init(prog_var) =  pa_datastruct__datastruct.
:- mode func_datastruct_init(in) = out is det.

func_datastruct_init(VAR) = DATA :-
	pa_datastruct__init(VAR,DATA).	
			
		
	
bottom(bottom).
top(top).

:- pred live_wrap(list(pa_datastruct__datastruct), live_set).
:- mode live_wrap(in,out) is det.

live_wrap(List, Live):-
	(	
		List = []
	->
		bottom(Live)
	;
		Live = live(List)
	).

get_datastructs(LiveSet, List):-
	(
		LiveSet = live(L)
	->
		List = L
	;
		bottom(LiveSet)
	->
		List = []
	;
		% top(LiveSet)
		require__error("(sr_live) get_datastructure: trying to collect datastructures from top-live-set.")
	).

union(LIVE_SETS, LIVE_SET) :- 
	list__foldl(
		union, 
		LIVE_SETS,
		bottom,
		LIVE_SET).

:- pred union(live_set, live_set, live_set).
:- mode union(in, in, out) is det.

union(L1, L2, L):-
	(
		L1 = live(D1),
		L2 = live(D2)
	->
		list__append(D1,D2,D),
		from_datastructs(D, L)
	;
		(top(L1) ; top(L2))
	->
		top(L)
	;
		bottom(L1)
	->
		L = L2
	;
		% bottom(L2)
		L = L1
	).	

is_live(Var,Live) :- 
	(
		Live = live(Datastructs)
	->
		pa_datastruct__init(Var,TopCel),
		list__member(TopCel, Datastructs)
	;
		Live = top
	->
		true
	;
		% Live = bottom
		fail
	).

		
is_live_datastruct(ModuleInfo, ProcInfo, Data, Live):- 
	(
		Live = live(Datastructs)
	->
		list__filter(
			pred(D::in) is semidet :- 
			    (pa_datastruct__less_or_equal(ModuleInfo,
					ProcInfo, Data, D, _S)),
			Datastructs,
			R),
		R = [_ | _ ]
		
	;
		Live = top
	->
		true
	;
		% Live = bottom
		fail
	).

project(VARS, Lin, Lout) :- 
	(
		Lin = live(Datastructs)
	->
		list__filter(
			pred(D::in) is semidet :- 
			    (
				list__member(D^var, VARS)
			    ),
			Datastructs, 
			FilteredDatastructs),
		live_wrap(FilteredDatastructs, Lout)
	;
		% bottom or top
		Lout = Lin
	).


