%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% module pa_prelim_run: implements some preliminary steps that have to 
% main author: nancy
%
% Implements some preliminary steps that have to be performed before the
% actual aliasing run:
%	1. setting up all the liveness fields in the goal_info's of all 
%	   the goals. 
%	2. setting up all the outscope fields in the goal_info's of all 
%	   the goals. 
%	Both steps, although very similar, are separated nevertheless.
%
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- module pa_prelim_run.

:- interface.

:- import_module hlds_module.

:- pred annotate_all_liveness_in_module(module_info::in, module_info::out,
		io__state::di, io__state::uo) is det.

:- pred annotate_all_outscope_vars_in_module(module_info::in,
		module_info::out) is det.

%-------------------------------------------------------------------%

:- implementation.

:- import_module list, map, set, std_util.
:- import_module hlds_pred, liveness. 
:- import_module hlds_goal, prog_data.


annotate_all_liveness_in_module(HLDSin, HLDSout) -->
	{ module_info_predids(HLDSin, PredIds0) }, 

	{ module_info_get_special_pred_map(HLDSin, SpecialPredMap) },
	{ map__values(SpecialPredMap, SpecialPredIds) },

	{ list__delete_elems(PredIds0, SpecialPredIds, PredIds) },

	list__foldl2(
		annotate_all_liveness_in_module_2,
		PredIds, 
		HLDSin, 
		HLDSout).

:- pred annotate_all_liveness_in_module_2(pred_id::in, module_info::in, 
		module_info::out, io__state::di, io__state::uo) is det.

annotate_all_liveness_in_module_2(PredId, HLDSin, HLDSout) -->
	{ module_info_pred_info( HLDSin, PredId, PredInfo0) },
	{ pred_info_procids(PredInfo0, ProcIds) }, 
	list__foldl2(annotate_all_liveness_in_pred(PredId, HLDSin),
			ProcIds, PredInfo0, PredInfo),
	{ module_info_set_pred_info( HLDSin, PredId, PredInfo, HLDSout) }.

:- pred annotate_all_liveness_in_pred(pred_id::in, module_info::in, 
		proc_id::in, pred_info::in, pred_info::out,
		io__state::di, io__state::uo) is det.

annotate_all_liveness_in_pred(PredId, HLDS, ProcId, PredInfo0, PredInfo) -->
	{ pred_info_procedures(PredInfo0, Procedures0) },
	{ map__lookup(Procedures0, ProcId, ProcInfo0) },

	liveness__detect_liveness_proc(PredId, ProcId, HLDS, ProcInfo0,
			ProcInfo),

	{ map__det_update(Procedures0, ProcId, ProcInfo, Procedures) },
	{ pred_info_set_procedures(PredInfo0, Procedures, PredInfo) }.


%-------------------------------------------------------------------%

annotate_all_outscope_vars_in_module(HLDSin, HLDSout) :- 
	module_info_predids(HLDSin, PredIds), 
	list__foldl(annotate_all_outscope_vars_in_module_2,
			PredIds, HLDSin, HLDSout).

:- pred annotate_all_outscope_vars_in_module_2(pred_id, module_info, 
		module_info).	
:- mode annotate_all_outscope_vars_in_module_2(in, in, out) is det.

annotate_all_outscope_vars_in_module_2(PredId, HLDSin, HLDSout ):- 
	module_info_pred_info(HLDSin, PredId, PredInfo0),
	pred_info_procids(PredInfo0, ProcIds), 
	list__foldl(annotate_all_outscope_vars_in_pred,
			ProcIds, PredInfo0, PredInfo),
	module_info_set_pred_info(HLDSin, PredId, PredInfo, HLDSout).

:- pred annotate_all_outscope_vars_in_pred(proc_id, pred_info, pred_info).
:- mode annotate_all_outscope_vars_in_pred(in, in, out) is det.

annotate_all_outscope_vars_in_pred(ProcId, PredInfo0, PredInfo) :- 
	pred_info_procedures(PredInfo0, Procedures0),
	map__lookup(Procedures0, ProcId, ProcInfo0 ), 
	proc_info_goal(ProcInfo0, Goal0 ), 
	set__init(Outscope), 
	annotate_all_outscope_vars_in_goal(Goal0, Outscope, Goal, _NewOutscope),
	proc_info_set_goal(ProcInfo0, Goal, ProcInfo),
	map__det_update(Procedures0, ProcId, ProcInfo, Procedures), 
	pred_info_set_procedures(PredInfo0, Procedures, PredInfo).

:- pred annotate_all_outscope_vars_in_goal(hlds_goal, set(prog_var), 
		hlds_goal, set(prog_var)).
:- mode annotate_all_outscope_vars_in_goal(in, in, out, out) is det.

annotate_all_outscope_vars_in_goal(Goal0, Outscope, Goal, NewOutscope) :-
	Goal0 = Expr0 - Info0, 
	(
		% 1. conjunction
		Expr0 = conj( Goals0 )
	->
		list__map_foldl( 
			(pred(G0::in, G::out, OSin::in, OSout::out) is det :- 
				annotate_all_outscope_vars_in_goal(G0,
						OSin, G, OSout)
			), Goals0, Goals, Outscope, _LastOutscope),
		Expr = conj(Goals)
	;
		Expr0 = disj(Goals0, SM)
	->
		list__map(
			(pred(G0::in, G::out) is det :- 
				annotate_all_outscope_vars_in_goal(G0,
						Outscope, G, _)
			), Goals0, Goals),
		Expr = disj(Goals, SM)
	;
		Expr0 = switch(A, B, Cases0, D)
	->
		list__map(
			(pred( C0::in, C::out) is det :- 
				C0 = case(ConsId, G0),
				annotate_all_outscope_vars_in_goal(G0,
						Outscope, G, _),
				C = case(ConsId, G)
			), Cases0, Cases),
		Expr = switch(A, B, Cases, D)
	;
		Expr0 = if_then_else(Vars, Cond0, Then0, Else0, SM) 
	->
		annotate_all_outscope_vars_in_goal(Cond0, Outscope, Cond,
				CondOutscope),
		annotate_all_outscope_vars_in_goal(Then0, CondOutscope,
				Then, _), 
		annotate_all_outscope_vars_in_goal(Else0, Outscope, Else, _),
		Expr = if_then_else(Vars, Cond, Then, Else, SM)
	;
		Expr0 = not(NegGoal0)
	->
		annotate_all_outscope_vars_in_goal(NegGoal0, Outscope,
				NegGoal, _),
		Expr = not(NegGoal)
	;
		Expr0 = some(Vars, CR, SomeGoal0)
	->
		annotate_all_outscope_vars_in_goal(SomeGoal0, Outscope,
				SomeGoal, _),
		Expr = some(Vars, CR, SomeGoal)
	;
		Expr = Expr0
	),
	goal_info_get_nonlocals(Info0, NL), 
	set__union(Outscope, NL, NewOutscope), 
	goal_info_set_outscope(Info0, NewOutscope, Info),	
	Goal = Expr - Info.
