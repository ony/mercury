%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module sr_fixpoint_table: definition of the fixpoint table used by
% 	sr_indirect.
% main author: nancy

:- module sr_fixpoint_table.

:- interface.

%-------------------------------------------------------------------%

% library modules.
:- import_module list.

% XXX parent modules
:- import_module hlds.

% compiler modules. 
:- import_module hlds__hlds_pred.
:- import_module sr_data.
:- import_module hlds__hlds_goal, hlds__hlds_module. 

:- type table.

:- pred sr_fixpoint_table_init(module_info::in, list(pred_proc_id)::in,
			table::out) is det.

	% the datastructure keeps track of the number of fixpoint runs
	% performed, this predicates adds one. 
:- pred sr_fixpoint_table_new_run(table::in, 
				table::out) is det.

:- pred sr_fixpoint_table_which_run(table::in, 
				int::out) is det.

	% check whether all entries are stable. If so, one has reached
	% a fixpoint
:- pred sr_fixpoint_table_all_stable(table:: in) is semidet.

	% at the end of the analysis of one single pred_proc_id, 
	% the new exit reuse information is stored. This might
	% change the stability of the table. 
	% if the pred_proc_id is not in the table --> error
:- pred sr_fixpoint_table_new_reuse(pred_proc_id, memo_reuse, 
			hlds_goal__hlds_goal,
			table, table).
:- mode sr_fixpoint_table_new_reuse(in, in, in, in, out) is det.

	% retreive the reuse information of a given
	% pred_proc_id. If this information is not available,
	% the general character of the fixpoint-table will be
	% set to `recursive'
	% if the pred_proc_id is not in the table --> fail
:- pred sr_fixpoint_table_get_reuse(pred_proc_id, memo_reuse, 
			table, table).
:- mode sr_fixpoint_table_get_reuse(in, out, in, out) is semidet.

	% retreive reuse information, without changing the
	% table. To be used after fixpoint has been reached. 
:- pred sr_fixpoint_table_get_final_reuse(pred_proc_id, memo_reuse, 
						hlds_goal__hlds_goal, 
						table).
:- mode sr_fixpoint_table_get_final_reuse(in, out, out, in) is det.


%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
:- implementation.

:- import_module std_util, require. 

:- type fixpoint_entry ---> 
			sr_fp(
				memo_reuse, 
			   	hlds_goal__hlds_goal
			).

:- pred fixpoint_entry_equal(fixpoint_entry, fixpoint_entry).
:- mode fixpoint_entry_equal(in, in) is semidet.

fixpoint_entry_equal(A, B) :- 
	A = sr_fp(TRA, _), 
	B = sr_fp(TRB, _), 
	sr_data__memo_reuse_equal(TRA, TRB).

:- pred pick_reuse_information(module_info, pred_proc_id, fixpoint_entry).
:- mode pick_reuse_information(in, in, out) is det.

pick_reuse_information(HLDS, PredProc, Entry) :- 
	module_info_pred_proc_info(HLDS, PredProc, _PredInfo, ProcInfo),
	proc_info_reuse_information(ProcInfo, Memo), 
	proc_info_goal(ProcInfo, Goal), 
	Entry = sr_fp(Memo, Goal).



:- import_module fixpoint_table.

:- type table == 
		fixpoint_table(pred_proc_id, fixpoint_entry).

sr_fixpoint_table_init(HLDS, PredProcs, Table) :- 
	fp_init(
		pred(K::in, E::out) is det:- 
			(
				pick_reuse_information(HLDS, K, E)
			),
		PredProcs,
		Table
		).

sr_fixpoint_table_new_run(Tin, Tout) :-
	fp_new_run(Tin,Tout).

sr_fixpoint_table_which_run(Tin, Run) :-
	Run = fp_which_run(Tin).

sr_fixpoint_table_all_stable(TABLE) :-
	fp_stable(TABLE).

sr_fixpoint_table_new_reuse(PRED_PROC_ID, TREUSE, GOAL, Tin, Tout) :-
	ENTRY = sr_fp(TREUSE, GOAL), 
	fp_add(fixpoint_entry_equal, PRED_PROC_ID, ENTRY, Tin, Tout).

sr_fixpoint_table_get_reuse(PRED_PROC_ID, TREUSE, Tin, Tout) :-
	fp_get(PRED_PROC_ID, ENTRY, Tin, Tout),
	ENTRY = sr_fp(TREUSE, _GOAL).

sr_fixpoint_table_get_final_reuse(PRED_PROC_ID, TREUSE, GOAL, T):-
	fp_get_final(PRED_PROC_ID, ENTRY, T),
	ENTRY = sr_fp(TREUSE, GOAL).



