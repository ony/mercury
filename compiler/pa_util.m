%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_util: extra datastructures and predicates needed by the
%		  KUL aliasing pass
% main author: nancy

:- module pa_util.

:- interface.

%-----------------------------------------------------------------------------%

% library modules. 
:- import_module list.

% XXX parent modules
:- import_module hlds.
% compiler modules
:- import_module hlds__hlds_pred.
:- import_module pa_alias_as.

:- type pa_fixpoint_table.

:- pred pa_fixpoint_table_init(list(pred_proc_id)::in,
			pa_fixpoint_table::out) is det.

	% the datastructure keeps track of the number of fixpoint runs
	% performed, this predicates adds one. 
:- pred pa_fixpoint_table_new_run(pa_fixpoint_table::in, pa_fixpoint_table::out) is det.

:- pred pa_fixpoint_table_which_run(pa_fixpoint_table::in, int::out) is det.

	% check whether all entries are stable. If so, one has reached
	% a fixpoint
:- pred pa_fixpoint_table_all_stable(pa_fixpoint_table:: in) is semidet.

	% at the end of the analysis of one single pred_proc_id, 
	% the new exit alias information is stored. This might
	% change the stability of the table. 
	% if the pred_proc_id is not in the table --> error
:- pred pa_fixpoint_table_new_as(module_info, proc_info, 
			pred_proc_id, alias_as, 
			pa_fixpoint_table, pa_fixpoint_table).
:- mode pa_fixpoint_table_new_as(in, in, in, in, in, out) is det.

	% retreive the alias abstract substitution of a given
	% pred_proc_id. If this information is not available,
	% the general character of the fixpoint-table will be
	% set to `recursive'
	% if the pred_proc_id is not in the table --> fail
:- pred pa_fixpoint_table_get_as(pred_proc_id, alias_as, 
			pa_fixpoint_table, pa_fixpoint_table).
:- mode pa_fixpoint_table_get_as(in, out, in, out) is semidet.

	% retreive alias_as information, without changing the
	% table. To be used after fixpoint has been reached. 
:- pred pa_fixpoint_table_get_final_as(pred_proc_id, alias_as, 
						pa_fixpoint_table).
:- mode pa_fixpoint_table_get_final_as(in, out, in) is det.

:- pred pa_fixpoint_table_get_final_as_semidet(pred_proc_id, alias_as, 
						pa_fixpoint_table).
:- mode pa_fixpoint_table_get_final_as_semidet(in, out, in) is semidet.


%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
:- implementation.

:- type pa_fixpoint_table == 
		fixpoint_table(pred_proc_id,
				pa_alias_as__alias_as).

:- import_module fixpoint_table.

:- pred wrapped_init(pred_proc_id, pa_alias_as__alias_as).
:- mode wrapped_init(in, out) is det.
wrapped_init(_, E) :- pa_alias_as__init(E).

pa_fixpoint_table_init(KEYS, TABLE):- 
	fp_init(wrapped_init, KEYS, TABLE).


pa_fixpoint_table_new_run(Tin, Tout) :-
	fp_new_run(Tin,Tout).

pa_fixpoint_table_which_run(Tin, Run) :-
	Run = fp_which_run(Tin).

pa_fixpoint_table_all_stable(TABLE) :-
	fp_stable(TABLE).

pa_fixpoint_table_new_as(ModuleInfo, ProcInfo, 
				PRED_PROC_ID, ALIAS_AS, Tin, Tout) :-
	fp_add(
		pred(TabledElem::in, Elem::in) is semidet :-
		(
			pa_alias_as__less_or_equal(ModuleInfo, ProcInfo, 
					Elem, TabledElem)
		), 
		PRED_PROC_ID, ALIAS_AS, Tin, Tout).

pa_fixpoint_table_get_as(PRED_PROC_ID, ALIAS_AS, Tin, Tout) :-
	fp_get(PRED_PROC_ID, ALIAS_AS, Tin, Tout).

pa_fixpoint_table_get_final_as(PRED_PROC_ID, ALIAS_AS, T):-
	fp_get_final(PRED_PROC_ID, ALIAS_AS, T).

pa_fixpoint_table_get_final_as_semidet(PRED_PROC_ID, ALIAS_AS, T):-
	fp_get_final_semidet(PRED_PROC_ID, ALIAS_AS, T). 

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- interface.

% XXX parent modules
:- import_module parse_tree.

:- import_module hlds__hlds_module, hlds__hlds_pred, list.
:- import_module parse_tree__prog_data.

:- pred arg_types_are_all_primitive(module_info, pred_info).
:- mode arg_types_are_all_primitive(in,in) is semidet.

:- pred types_are_primitive(module_info::in, list(type)::in) is semidet.

:- implementation. 

% XXX parent modules
:- import_module check_hlds. 
:- import_module check_hlds__type_util.

arg_types_are_all_primitive(HLDS, PredInfo):-
        hlds_pred__pred_info_arg_types(PredInfo, ArgTypes),
        types_are_primitive(HLDS, ArgTypes).

types_are_primitive(HLDS, TYPES) :- 
        list__filter(pred(TYPE::in) is semidet :-
		(
			type_util__type_is_atomic(TYPE,HLDS)
		),
		TYPES,
		_TrueList, 
		[]).

