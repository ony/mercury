%-----------------------------------------------------------------------------%
% Copyright (C) 1996-2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module sr_reuse_util: extra datastructures and predicates needed by the
%		datastructure-reuse analysis
% main author: nancy

:- module sr_reuse_util.

:- interface.

%-------------------------------------------------------------------%

:- import_module list.
:- import_module hlds_pred.
:- import_module sr_reuse.
:- import_module hlds_goal. 

:- type sr_fixpoint_table.

:- pred sr_fixpoint_table_init(list(pred_proc_id)::in,
			sr_fixpoint_table::out) is det.

	% the datastructure keeps track of the number of fixpoint runs
	% performed, this predicates adds one. 
:- pred sr_fixpoint_table_new_run( sr_fixpoint_table::in, 
				sr_fixpoint_table::out) is det.

:- pred sr_fixpoint_table_which_run( sr_fixpoint_table::in, 
				int::out) is det.

	% check whether all entries are stable. If so, one has reached
	% a fixpoint
:- pred sr_fixpoint_table_all_stable( sr_fixpoint_table:: in ) is semidet.

	% at the end of the analysis of one single pred_proc_id, 
	% the new exit reuse information is stored. This might
	% change the stability of the table. 
	% if the pred_proc_id is not in the table --> error
:- pred sr_fixpoint_table_new_reuse( pred_proc_id, tabled_reuse, 
			hlds_goal__hlds_goal,
			sr_fixpoint_table, sr_fixpoint_table).
:- mode sr_fixpoint_table_new_reuse( in, in, in, in, out) is det.

	% retreive the reuse information of a given
	% pred_proc_id. If this information is not available,
	% the general character of the fixpoint-table will be
	% set to `recursive'
	% if the pred_proc_id is not in the table --> fail
:- pred sr_fixpoint_table_get_reuse( pred_proc_id, tabled_reuse, 
			sr_fixpoint_table, sr_fixpoint_table).
:- mode sr_fixpoint_table_get_reuse( in, out, in, out) is semidet.

	% retreive reuse information, without changing the
	% table. To be used after fixpoint has been reached. 
:- pred sr_fixpoint_table_get_final_reuse( pred_proc_id, tabled_reuse, 
						hlds_goal__hlds_goal, 
						sr_fixpoint_table).
:- mode sr_fixpoint_table_get_final_reuse( in, out, out, in) is det.


%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
:- implementation.

:- import_module std_util, require. 

:- type fixpoint_entry ---> 
			sr_fp( 
				sr_reuse__tabled_reuse, 
			   	maybe(hlds_goal__hlds_goal)
			).

:- pred fixpoint_entry_equal( fixpoint_entry, fixpoint_entry ).
:- mode fixpoint_entry_equal( in, in) is semidet.

fixpoint_entry_equal(A, B) :- 
	A = sr_fp( TRA, _), 
	B = sr_fp( TRB, _), 
	sr_reuse__tabled_reuse_equal(TRA, TRB).

:- pred fixpoint_entry_init( fixpoint_entry ).
:- mode fixpoint_entry_init( out ) is det.

fixpoint_entry_init( A ):- 
	A = sr_fp( TRA, no), 
	sr_reuse__tabled_reuse_init( TRA ).

:- type sr_fixpoint_table == 
		fixpoint_table__fixpoint_table( pred_proc_id,
				fixpoint_entry ).

:- import_module fixpoint_table.

:- instance tc_element(fixpoint_entry) where [
	pred(equal/2) is fixpoint_entry_equal,
	pred(init/1) is fixpoint_entry_init
	].

sr_fixpoint_table_init( KEYS, TABLE):- 
	fp_init( KEYS, TABLE).

sr_fixpoint_table_new_run( Tin, Tout ) :-
	fp_new_run(Tin,Tout).

sr_fixpoint_table_which_run( Tin, Run ) :-
	fp_which_run(Tin,Run).

sr_fixpoint_table_all_stable( TABLE ) :-
	fp_stable(TABLE).

sr_fixpoint_table_new_reuse( PRED_PROC_ID, TREUSE, GOAL, Tin, Tout) :-
	ENTRY = sr_fp( TREUSE, yes(GOAL) ), 
	fp_add(PRED_PROC_ID, ENTRY, Tin, Tout).

sr_fixpoint_table_get_reuse( PRED_PROC_ID, TREUSE, Tin, Tout) :-
	fp_get(PRED_PROC_ID, ENTRY, Tin, Tout),
	ENTRY = sr_fp( TREUSE, _MAYBEGOAL ).

sr_fixpoint_table_get_final_reuse( PRED_PROC_ID, TREUSE, GOAL, T ):-
	fp_get_final( PRED_PROC_ID, ENTRY, T),
	ENTRY = sr_fp( TREUSE, MAYBEGOAL ),
	(
		MAYBEGOAL = yes(GOAL0)
	->
		GOAL = GOAL0
	;
		require__error("(sr_reuse_util) sr_fixpoint_table_get_final_reuse: no goal in table")
	).
	



