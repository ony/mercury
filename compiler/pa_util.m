%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_util: 
% 	* Defines the fixpoint table used in the analysis of possible
% 	aliases.
% 	* Defines some type-related predicates (should be moved to somewhere
% 	else though). XXX
%		  
% main author: nancy

:- module possible_alias__pa_util.

:- interface.

:- import_module hlds__hlds_pred.
:- import_module possible_alias__pa_alias_as.

:- import_module list.

:- type pa_fixpoint_table.

	% Initialise the fixpoint table for the given set of pred_proc_id's. 
:- pred pa_fixpoint_table_init(list(pred_proc_id)::in,
		pa_fixpoint_table::out) is det.

	% Add the results of a new analysis pass to the already existing
	% fixpoint table. 
:- pred pa_fixpoint_table_new_run(pa_fixpoint_table::in, 
		pa_fixpoint_table::out) is det.

	% The fixpoint table keeps track of the number of analysis passes. This
	% predicate returns this number.
:- pred pa_fixpoint_table_which_run(pa_fixpoint_table::in, int::out) is det.

	% A fixpoint is reached if all entries in the table are stable,
	% i.e. haven't been modified by the last analysis pass. 
:- pred pa_fixpoint_table_all_stable(pa_fixpoint_table::in) is semidet.

	% Enter the newly computed alias description for a given procedure.
	% If the description is different from the one that was already stored
	% for that procedure, the stability of the fixpoint table is set to
	% "unstable". 
	% Aborts if the procedure is not already in the fixpoint table. 
:- pred pa_fixpoint_table_new_as(module_info::in, proc_info::in, 
		pred_proc_id::in, alias_as::in, 
		pa_fixpoint_table::in, pa_fixpoint_table::out) is det.

	% Retreive the alias description of a given
	% pred_proc_id. If this information is not available, this means that
	% the set of pred_proc_id's to which the fixpoint table relates are
	% mutually recursive, hence the table is characterised as recursive. 
	% Fails if the procedure is not in the table. 
:- pred pa_fixpoint_table_get_as(pred_proc_id::in, alias_as::out, 
		pa_fixpoint_table::in, pa_fixpoint_table::out) is semidet.

	% Retreive alias_as information, without changing the
	% table. To be used after fixpoint has been reached. 
	% Aborts if the procedure is not in the table.
:- pred pa_fixpoint_table_get_final_as(pred_proc_id::in, alias_as::out, 
		pa_fixpoint_table::in) is det.

	% Same as pa_fixpoint_table_get_final_as, yet fails instead of aborting
	% if the procedure is not in the table.
:- pred pa_fixpoint_table_get_final_as_semidet(pred_proc_id::in, alias_as::out, 
		pa_fixpoint_table::in) is semidet.


%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
:- implementation.

:- import_module fixpoint_table.

:- type pa_fixpoint_table == 
		fixpoint_table(pred_proc_id,
				pa_alias_as__alias_as).


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

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module parse_tree__prog_data.

:- import_module list.

:- pred arg_types_are_all_primitive(module_info, pred_info).
:- mode arg_types_are_all_primitive(in,in) is semidet.

:- pred types_are_primitive(module_info::in, list(type)::in) is semidet.

:- implementation. 

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

