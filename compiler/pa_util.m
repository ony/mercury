%-----------------------------------------------------------------------------%
% Copyright (C) 1996-2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_util: extra datastructures and predicates needed by the
%		  KUL aliasing pass
% main author: nancy

:- module pa_util.

:- interface.

%-------------------------------------------------------------------%

:- import_module hlds_pred.
:- import_module pa_alias_as.
:- import_module list.

:- type pa_fixpoint_table.

:- pred pa_fixpoint_table_init(list(pred_proc_id)::in,
			pa_fixpoint_table::out) is det.

	% the datastructure keeps track of the number of fixpoint runs
	% performed, this predicates adds one. 
:- pred pa_fixpoint_table_new_run( pa_fixpoint_table::in, pa_fixpoint_table::out) is det.

:- pred pa_fixpoint_table_which_run( pa_fixpoint_table::in, int::out) is det.

	% check whether all entries are stable. If so, one has reached
	% a fixpoint
:- pred pa_fixpoint_table_all_stable( pa_fixpoint_table:: in ) is semidet.

	% at the end of the analysis of one single pred_proc_id, 
	% the new exit alias information is stored. This might
	% change the stability of the table. 
	% if the pred_proc_id is not in the table --> error
:- pred pa_fixpoint_table_new_as( pred_proc_id, alias_as, 
			pa_fixpoint_table, pa_fixpoint_table).
:- mode pa_fixpoint_table_new_as( in, in, in, out) is det.

	% retreive the alias abstract substitution of a given
	% pred_proc_id. If this information is not available,
	% the general character of the fixpoint-table will be
	% set to `recursive'
	% if the pred_proc_id is not in the table --> fail
:- pred pa_fixpoint_table_get_as( pred_proc_id, alias_as, 
			pa_fixpoint_table, pa_fixpoint_table).
:- mode pa_fixpoint_table_get_as( in, out, in, out) is semidet.

	% retreive alias_as information, without changing the
	% table. To be used after fixpoint has been reached. 
:- pred pa_fixpoint_table_get_final_as( pred_proc_id, alias_as, 
						pa_fixpoint_table).
:- mode pa_fixpoint_table_get_final_as( in, out, in) is det.


%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
:- implementation.

:- type pa_fixpoint_table == 
		fixpoint_table( pred_proc_id,
				pa_alias_as__alias_as ).

:- import_module fixpoint_table.

:- instance tc_element(alias_as) where [
	pred(equal/2) is pa_alias_as__equal,
	pred(init/1) is pa_alias_as__init
	].

pa_fixpoint_table_init( KEYS, TABLE):- 
	fp_init( KEYS, TABLE).

pa_fixpoint_table_new_run( Tin, Tout ) :-
	fp_new_run(Tin,Tout).

pa_fixpoint_table_which_run( Tin, Run ) :-
	fp_which_run(Tin,Run).

pa_fixpoint_table_all_stable( TABLE ) :-
	fp_stable(TABLE).

pa_fixpoint_table_new_as( PRED_PROC_ID, ALIAS_AS, Tin, Tout) :-
	fp_add(PRED_PROC_ID, ALIAS_AS, Tin, Tout).

pa_fixpoint_table_get_as( PRED_PROC_ID, ALIAS_AS, Tin, Tout) :-
	fp_get(PRED_PROC_ID, ALIAS_AS, Tin, Tout).

pa_fixpoint_table_get_final_as( PRED_PROC_ID, ALIAS_AS, T ):-
	fp_get_final( PRED_PROC_ID, ALIAS_AS, T).


