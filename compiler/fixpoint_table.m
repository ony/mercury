%---------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%---------------------------------------------------------------------------%
% File: fixpoint_table.m
% Main author: nancy.

% This modules defines a generic table to be used for fixpoint computations. 
% For each key (usually pred_proc_id), it will map a given abstract
% substitution. Here the notion of abstract substitution is abstracted 
% away as a typeclass which required only two operations: equal and init.

:- module fixpoint_table.

:- interface.

:- import_module list.

:- typeclass tc_element(T) where [
	pred equal(T, T),
 	mode equal(in,in) is semidet,

	pred init(T),
	mode init(out) is det
].

:- type fixpoint_table( K, E ). 

	% initialise the table
	% The first parameter is a list of keys which will be allowed in 
	% the table. 
:- pred fp_init(list(K),fixpoint_table(K, E)) <= tc_element(E).
:- mode fp_init(in,out) is det.

	% inform the table that a new run has begun
:- pred fp_new_run(fixpoint_table(K, E),fixpoint_table(K, E)) <= tc_element(E).
:- mode fp_new_run(in,out) is det.

:- pred fp_which_run(fixpoint_table(K,E), int) <= tc_element(E).
:- mode fp_which_run(in,out) is det.

	% check whether a fixpoint has been reached
:- pred fp_stable(fixpoint_table(K, E)) <= tc_element(E).
:- mode fp_stable(in) is semidet.

	% add a new element (E) associated with key (K) to the table.
	%   - if an element is already recorded with that key, 
	%      * and if both elements are equal, then a fixpoint is obtained
	%        as far as this key is concerned
	%      * if the elements are different, fixpoint is not reached yet, 
	%	 and the new information is simply kept
	%   - if the element was not yet present in the table, add it
	%     to the table (which does not change the stability of the
	%     table) 
:- pred fp_add(K,E,fixpoint_table(K, E),fixpoint_table(K, E)) <= tc_element(E).
:- mode fp_add(in,in,in,out) is det.

	% retreive an element (E) associated with key (K) from the table.
	% This operation can change the state of the table if the element
	% is not yet present in the table. This means that we're facing
	% a recursive calltree. If the key is not an element of the
	% allowed keys, then the procedure will fail. 
:- pred fp_get(K,E,fixpoint_table(K, E),fixpoint_table(K, E)) <= tc_element(E).
:- mode fp_get(in,out,in,out) is semidet.

	% retreive an element (E) associated with key (K) from the table. 
	% The operation reports an error when the element is not present. 
:- pred fp_get_final(K,E,fixpoint_table(K,E)) <= tc_element(E).
:- mode fp_get_final(in,out,in) is det.

:- implementation. 

:- import_module bool, map, list, int.
:- import_module require.

:- type fixpoint_table( K, E ) --->
		ft(  
		     keys	:: list( K ),   % list of allowed keys
		     run	:: int, 	% number of runs
		     stable	:: bool,	% is stable (default = yes)
		     mapping 	:: map( K, E )
		).

fp_init( Ks, T ) :- 
	Run = 0,
	Stable = yes,
	map__init(Map),
	T = ft(Ks,Run,Stable,Map).

fp_new_run( T0, T0^run := NewRun ) :- 
	NewRun = T0^run + 1.
fp_which_run( T0, T0^run ).

fp_stable( T ) :- 
		T^stable = yes .
	
fp_add( INDEX, ELEM, Tin, Tout ) :- 
	Map = Tin^mapping, 
	Sin = Tin^stable,
	( 
		map__search( Map, INDEX, TabledELEM)
	->
		(
			equal(TabledELEM,ELEM)
		->
			S = yes
		;
			S = no 
		),
			% whether or not the tabled element is equal to
			% the new element, the final tabled element will 
			% always be set to the new one. This is handy
			% for performing the following trick: equality
			% can be checked on some partial piece of the 
			% elements (for deciding stability), but some other
			% part might have changed, a change that should 
			% become visible in the table too. 
			% (in fact this is necessary for the reuse-fixpoint
			% table where not only the reuses are kept (the
			% abstract substitution), but also the goal that
			% might have changed. 
		FinalTabledElem = ELEM,
		map__det_update( Map, INDEX, FinalTabledElem, MapOut)
	;
		S = Sin,
		map__det_insert( Map, INDEX, ELEM, MapOut)
	),
	Tout = (Tin^mapping := MapOut)^stable := S.

fp_get( INDEX, ELEM, Tin, Tout) :-
	List = Tin^keys, 
	list__member(INDEX,List), % can fail
	MAPin = Tin^mapping,
	Sin = Tin^stable,
	(	
		map__search( MAPin, INDEX, TabledELEM)
	->
		ELEM = TabledELEM,
		Sout = Sin,
		MAPout = MAPin
	;
		init(ELEM),
		Sout = no,
		map__det_insert(MAPin, INDEX, ELEM, MAPout)
	),
	Tout = (Tin^mapping := MAPout)^stable := Sout.

fp_get_final( INDEX, ELEM, T ) :- 
	(
		map__search( T^mapping, INDEX, TabledELEM)
	->
		ELEM = TabledELEM
	; 
		error("Internal error: fixpoint_table__fp_get_final/2")
	).
