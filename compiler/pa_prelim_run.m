%-----------------------------------------------------------------------------%
% Copyright (C) 1996-2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_prelim_run: implements some preliminary steps that have to 
%		be performed before the actual aliasing run:
%		1. setting up all the liveness fields in the goal_info's of all 
%		   the goals. 
%		2. setting up all the outscope fields in the goal_info's of all 
%		   the goals. 
%		Both steps, although very similar, are separated nevertheless. 
% main author: nancy

:- module pa_prelim_run.

:- interface.

:- import_module hlds_module.

:- pred annotate_all_liveness_in_module( module_info, module_info).
:- mode annotate_all_liveness_in_module( in, out) is det.

:- pred annotate_all_outscope_vars_in_module( module_info, module_info).
:- mode annotate_all_outscope_vars_in_module( in, out) is det.

%-------------------------------------------------------------------%

:- implementation.

:- import_module list, map, set, std_util.
:- import_module hlds_pred, liveness. 
:- import_module hlds_goal, prog_data.

annotate_all_liveness_in_module( HLDSin, HLDSout) :- 
	module_info_predids( HLDSin, PRED_IDS ), 
	list__foldl(
		annotate_all_liveness_in_module_2,
		PRED_IDS, 
		HLDSin, 
		HLDSout).

:- pred annotate_all_liveness_in_module_2( pred_id, module_info, 
		module_info).	
:- mode annotate_all_liveness_in_module_2( in, in, out) is det.

annotate_all_liveness_in_module_2( PredId, HLDSin, HLDSout ):- 
	module_info_pred_info( HLDSin, PredId, PredInfo),
	pred_info_procids( PredInfo, PROC_IDS), 
	list__foldl( 
		annotate_all_liveness_in_pred(PredId, HLDSin),
		PROC_IDS,
		PredInfo, 
		PredInfo_NEW),
	module_info_set_pred_info( HLDSin, PredId, PredInfo_NEW, HLDSout).

:- pred annotate_all_liveness_in_pred( pred_id, module_info, 
		proc_id, pred_info, pred_info).
:- mode annotate_all_liveness_in_pred( in, in, in, in, out) is det.

annotate_all_liveness_in_pred( PredId, HLDS, ProcId, PredInfo0, PredInfo) :- 
	pred_info_procedures( PredInfo0, Procedures0),
	map__lookup( Procedures0, ProcId, ProcInfo0), 
	liveness__detect_liveness_proc( ProcInfo0, PredId, HLDS, ProcInfo), 
	map__det_update( Procedures0, ProcId, ProcInfo, Procedures),
	pred_info_set_procedures( PredInfo0, Procedures, PredInfo).


%-------------------------------------------------------------------%

annotate_all_outscope_vars_in_module( HLDSin, HLDSout) :- 
	module_info_predids( HLDSin, PRED_IDS ), 
	list__foldl(
		annotate_all_outscope_vars_in_module_2,
		PRED_IDS, 
		HLDSin, 
		HLDSout).

:- pred annotate_all_outscope_vars_in_module_2( pred_id, module_info, 
		module_info).	
:- mode annotate_all_outscope_vars_in_module_2( in, in, out) is det.

annotate_all_outscope_vars_in_module_2( PredId, HLDSin, HLDSout ):- 
	module_info_pred_info( HLDSin, PredId, PredInfo),
	pred_info_procids( PredInfo, PROC_IDS), 
	list__foldl( 
		annotate_all_outscope_vars_in_pred,
		PROC_IDS,
		PredInfo, 
		PredInfo_NEW),
	module_info_set_pred_info( HLDSin, PredId, PredInfo_NEW, HLDSout).

:- pred annotate_all_outscope_vars_in_pred( proc_id, pred_info, pred_info).
:- mode annotate_all_outscope_vars_in_pred( in, in, out) is det.

annotate_all_outscope_vars_in_pred( ProcId, PredInfo0, PredInfo ):- 
	pred_info_procedures( PredInfo0, Procedures0),
	map__lookup( Procedures0, ProcId, ProcInfo0 ), 
	proc_info_goal( ProcInfo0, Goal0 ), 
	set__init( Outscope ), 
	annotate_all_outscope_vars_in_goal( Goal0, Outscope, Goal, _NewOutscope ),
	proc_info_set_goal( ProcInfo0, Goal, ProcInfo ),
	map__det_update( Procedures0, ProcId, ProcInfo, Procedures), 
	pred_info_set_procedures( PredInfo0, Procedures, PredInfo ).

:- pred annotate_all_outscope_vars_in_goal( hlds_goal, set(prog_var), 
						hlds_goal, set(prog_var)).
:- mode annotate_all_outscope_vars_in_goal( in, in, out, out) is det.

annotate_all_outscope_vars_in_goal( Goal0, Outscope, Goal, NewOutscope) :-
	Goal0 = Expr0 - Info0, 

	(
		% 1. conjunction
		Expr0 = conj( Goals0 )
	->
		list__map_foldl( 
			pred( G0::in, G::out, OSin::in, OSout::out ) is det :- 
			    (
				annotate_all_outscope_vars_in_goal( G0, OSin, G, OSout)
			    ),
			Goals0,
			Goals,
			Outscope, 
			_LastOutscope),
		Expr = conj( Goals )
	;
		Expr0 = disj( Goals0, SM )
	->
		list__map(
			pred( G0::in, G::out ) is det :- 
			    (
				annotate_all_outscope_vars_in_goal( G0, Outscope, G, _)
			    ),
			Goals0, 
			Goals),
		Expr = disj( Goals, SM )
	;
		Expr0 = switch( A, B, Cases0, D )
	->
		list__map(
			pred( C0::in, C::out) is det :- 
			    (
				C0 = case( CONS, G0 ),
				annotate_all_outscope_vars_in_goal( G0, Outscope, G, _),
				C = case( CONS, G)
			    ), 
			Cases0,
			Cases),
		Expr = switch( A, B, Cases, D)
	;
		Expr0 = if_then_else( Vars, Cond0, Then0, Else0, SM) 
	->
		annotate_all_outscope_vars_in_goal( Cond0, Outscope, Cond, CondOutscope),
		annotate_all_outscope_vars_in_goal( Then0, CondOutscope, Then, _), 
		annotate_all_outscope_vars_in_goal( Else0, Outscope, Else, _),
		Expr = if_then_else( Vars, Cond, Then, Else, SM)
	;
		Expr0 = not(NegGoal0)
	->
		annotate_all_outscope_vars_in_goal( NegGoal0, Outscope, NegGoal, _),
		Expr = not(NegGoal)
	;
		Expr0 = some( Vars, CR, SomeGoal0)
	->
		annotate_all_outscope_vars_in_goal( SomeGoal0, Outscope, SomeGoal, _),
		Expr = some(Vars, CR, SomeGoal)
	;
		Expr = Expr0
	),
	goal_info_get_nonlocals( Info0, NL ), 
	set__union( Outscope, NL, NewOutscope), 
	goal_info_set_outscope( Info0, NewOutscope, Info),	
	Goal = Expr - Info.

