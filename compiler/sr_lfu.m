%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module sr_lfu: implements the process of annotating each program point
% 		 with Local Forward Use (LFU) information. 
% main author: nancy

:- module structure_reuse__sr_lfu.

:- interface.

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred. 

:- import_module io.

:- pred sr_lfu__lfu_pass(module_info, module_info, io__state, io__state).
:- mode sr_lfu__lfu_pass(in, out, di, uo) is det.

:- pred sr_lfu__process_proc(proc_info::in, proc_info::out) is det.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%

:- implementation. 

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_llds.
:- import_module hlds__passes_aux.
:- import_module libs__globals.
:- import_module libs__options.
:- import_module ll_backend__liveness.
:- import_module parse_tree__prog_data.

:- import_module list, map, bool, set, varset.
:- import_module string.
:- import_module std_util, require.


sr_lfu__lfu_pass(HLDSin , HLDSout) --> 
	% get all the predicate id's 
	{ hlds_module__module_info_predids(HLDSin, ALL_PRED_IDS) },
	% get all the id's of special predicates
	{ hlds_module__module_info_get_special_pred_map(HLDSin, SPEC_MAP) },
	{ map__values(SPEC_MAP, SPEC_PRED_IDS) }, 
	% remove the special pred_ids from the set of pred_ids
	{ list__delete_elems(ALL_PRED_IDS, SPEC_PRED_IDS, PRED_IDS0) },
	% filter out the predids of predicates not defined in this 
	% module 
	{ list__filter(
		pred_defined_in_this_module(HLDSin),
		PRED_IDS0, PRED_IDS) },

	list__foldl2(annotate_lfu_in_pred, PRED_IDS, HLDSin, HLDSout).

:- pred pred_defined_in_this_module(module_info, pred_id).
:- mode pred_defined_in_this_module(in,in) is semidet.

pred_defined_in_this_module(HLDS,ID):-
	not(hlds_module__pred_not_defined_in_this_module(HLDS,ID)).

:- pred annotate_lfu_in_pred(pred_id, module_info, module_info, io__state,
		io__state).
:- mode annotate_lfu_in_pred(in,in,out,di,uo) is det.

annotate_lfu_in_pred(PRED_ID, HLDSin, HLDSout) --> 
	{ hlds_module__module_info_pred_info(HLDSin, PRED_ID, PredInfo) }, 
	globals__io_lookup_bool_option(very_verbose, VeryVerbose),
	(
		{ VeryVerbose = yes }
	->
		passes_aux__write_pred_progress_message(
			"% LFU-annotating ", 
			PRED_ID, 
			HLDSin)
	;
		[]
	),

	% fetching the procids
	{ pred_info_procids(PredInfo, PROC_IDS) },
	
	% handling all procids
	{ list__foldl(annotate_lfu_in_proc(HLDSin, PRED_ID), 
			PROC_IDS, PredInfo, NewPredInfo) },

	% and updating the module_info with the new predinfo-state. 
	{ module_info_set_pred_info(HLDSin, PRED_ID, NewPredInfo, 
			HLDSout) }.


:- pred annotate_lfu_in_proc(module_info, pred_id, proc_id, 
		pred_info, pred_info).
:- mode annotate_lfu_in_proc(in, in, in, in, out) is det.

annotate_lfu_in_proc(_HLDS, _PRED_ID, PROC_ID, PredInfo0, PredInfo) :- 
	pred_info_procedures(PredInfo0, Procedures0)  , 
	map__lookup(Procedures0, PROC_ID, ProcInfo0)  , 
	% fill the 4 liveness-related fields:
	/** this should already have been done in the alias-pass 
	liveness__detect_liveness_proc(ProcInfo0, PRED_ID, HLDS, 
					ProcInfo01) , 
	**/
	ProcInfo01 = ProcInfo0,

	sr_lfu__process_proc(ProcInfo01, ProcInfo),

	map__det_update(Procedures0, PROC_ID, ProcInfo, Procedures) ,
	pred_info_set_procedures(PredInfo0, Procedures, PredInfo).

process_proc(ProcInfo01, ProcInfo) :-
	proc_info_goal(ProcInfo01, Goal0),

		% the set of variables initially instantiated 
	proc_info_liveness_info(ProcInfo01, InstVars0), 
		% the set of variables initially dead (meaning 
		% syntactically dead)
	set__init(DeadVars0),
	
		% annotate each of the goals	
	annotate_lfu_in_goal(InstVars0, DeadVars0, Inst, Dead, Goal0, Goal01), 
	

	% explicitly make the lfu-set of the top-level goal to be 
	% empty
	% set__init(LFU),
	set__difference(Inst,Dead,LFU),
	Goal01 = Expr01 - Info01, 
	goal_info_set_lfu(LFU, Info01, Info), 
	Goal = Expr01 - Info, 

	% compute global use: global use = intersect(LFU, headvars)
	proc_info_headvars(ProcInfo01, HeadVars), 
	set__list_to_set(HeadVars, HeadVarsSet),
	set__intersect(LFU, HeadVarsSet, GlobalUse),

	% We update the latest procinfo, as the information derived
	% by the liveness pass is still needed (resume-point used
	% by the lbu-pass). 

	proc_info_set_global_use(ProcInfo01, GlobalUse, ProcInfo02),
	proc_info_set_goal(ProcInfo02, Goal, ProcInfo).


	% annotate_lfu_in_goal(InstantiatedVars0, DiedVars0, 
	%		       InstantiatedVars, DiedVars, Goalin, Goalout).
:- pred annotate_lfu_in_goal(set(prog_var), set(prog_var), 
		set(prog_var), set(prog_var),
		hlds_goal, hlds_goal).
:- mode annotate_lfu_in_goal(in, in, out, out, in, out) is det.

annotate_lfu_in_goal(Inst0, Dead0, Inst, Dead, Goal0, Goal):- 
	Goal0 = Expr0 - Info0,

	(
		goal_is_atomic(Expr0)
	->
		calculateInstDead(Info0, Inst0, Dead0, Inst, Dead),
		set__difference(Inst,Dead,LFU),
		goal_info_set_lfu(LFU, Info0, Info),
		Goal = Expr0 - Info
	;
		annotate_lfu_in_goal_2(Inst0, Dead0, Inst, Dead, Goal0, Goal)
	).


	% calculateInstDead(info, instantiatedvars0, deadvars0, 
	%		instantiatedvars, deadvars)
:- pred calculateInstDead(hlds_goal_info, set(prog_var), set(prog_var),
		set(prog_var), set(prog_var)).
:- mode calculateInstDead(in, in, in, out, out) is det.

calculateInstDead(Info, Inst0, Dead0, Inst, Dead) :- 
	% Inst = Inst0 + birth-set
	% Dead = Dead0 + death-set 
	goal_info_get_pre_births(Info, PreBirths), 
	goal_info_get_post_births(Info, PostBirths), 
	goal_info_get_post_deaths(Info, PostDeaths),
	goal_info_get_pre_deaths(Info, PreDeaths), 

	set__union(PreBirths, PostBirths, Births),
	set__union(PreDeaths, PostDeaths, Deaths), 
	
	set__union(Births, Inst0, Inst),
	set__union(Deaths, Dead0, Dead).

:- pred annotate_lfu_in_goal_2(set(prog_var), set(prog_var), 
		set(prog_var), set(prog_var), 
		hlds_goal, hlds_goal).
:- mode annotate_lfu_in_goal_2(in, in, out, out, in, out) is det.

annotate_lfu_in_goal_2(Inst0, Dead0, Inst, Dead, TopGoal0, TopGoal) :-
	TopGoal0 = Expr0 - Info0,
	(
		Expr0 = conj(Goals0)
	->
		annotate_lfu_in_conj(Inst0, Dead0, Inst, Dead, Goals0, Goals),
		Expr = conj(Goals)
	;
		Expr0 = switch(A,B,Cases0)
	->
		annotate_lfu_in_cases(Inst0, Dead0, Inst, Dead, Cases0, Cases),
		Expr = switch(A,B,Cases)
	;
		Expr0 = disj(Disj0)
	->
		annotate_lfu_in_disjs(Inst0, Dead0, Inst, Dead, Disj0, Disj),
		Expr = disj(Disj)
	;
		Expr0 = not(Goal0)
	->
		annotate_lfu_in_goal(Inst0, Dead0, Inst, Dead, Goal0, Goal),
		Expr = not(Goal)
	;
		Expr0 = some(V, C, Goal0)
	->
		annotate_lfu_in_goal(Inst0, Dead0, Inst, Dead, Goal0, Goal),
		Expr = some(V,C,Goal)
	;
		Expr0 = if_then_else(V, COND0, THEN0, ELSE0)
	->
		annotate_lfu_in_goal(Inst0, Dead0, Inst01, Dead01, 
					COND0, COND), 
		annotate_lfu_in_goal(Inst01, Dead01, Inst1, Dead1, 
					THEN0, THEN),
		annotate_lfu_in_goal(Inst0, Dead0, Inst2, Dead2, 
					ELSE0, ELSE),
		set__union(Inst1,Inst2, Inst),
		set__union(Dead1, Dead2, Dead),
		Expr = if_then_else(V, COND, THEN, ELSE)
	;
		error("atomic call in annotate_lfu_in_goal_2"),
		Expr = Expr0
	),
	set__difference(Inst,Dead,LFU),
	goal_info_set_lfu(LFU, Info0, Info),
	TopGoal = Expr - Info. 

:- pred annotate_lfu_in_conj(set(prog_var), set(prog_var),
				set(prog_var), set(prog_var), 
				list(hlds_goal), list(hlds_goal)).
:- mode annotate_lfu_in_conj(in, in, out, out, in, out) is det.

annotate_lfu_in_conj(Inst0, Dead0, Inst, Dead, Goals0, Goals) :- 
	map_foldl2(
		pred(Goal0::in, Goal::out, 
		      I0::in, I::out,
		      D0::in, D::out) is det :- 
			(annotate_lfu_in_goal(I0, D0, I, D, Goal0, Goal)), 
		Goals0, 
		Goals, 
		Inst0, Inst,
		Dead0, Dead).

:- pred annotate_lfu_in_cases(set(prog_var), set(prog_var), 
			 	set(prog_var), set(prog_var), 
				list(case), list(case)).
:- mode annotate_lfu_in_cases(in, in, out, out, in, out) is det.

annotate_lfu_in_cases(Inst0, Dead0, Inst, Dead, Cases0, Cases) :- 
	map_foldl2(
		pred(Case0::in, Case::out, 
			I0::in, I::out, 
			D0::in, D::out) is det :- 
			(Case0 = case(Cons,Goal0), 
			  annotate_lfu_in_goal(Inst0, Dead0, NI, ND ,
				Goal0, Goal), 
			  Case = case(Cons,Goal), 
			  set__union(I0, NI, I), 
			  set__union(D0, ND, D)), 
		Cases0, 
		Cases, 
		Inst0, Inst, 
		Dead0, Dead).

:- pred annotate_lfu_in_disjs(set(prog_var), set(prog_var),
			       	set(prog_var), set(prog_var), 
				list(hlds_goal), list(hlds_goal)).
:- mode annotate_lfu_in_disjs(in, in, out, out, in, out) is det.

annotate_lfu_in_disjs(Inst0, Dead0, Inst, Dead, Goals0, Goals) :-
	map_foldl2(
		pred(Goal0::in, Goal::out, 
			I0::in, I::out, 
			D0::in, D::out) is det :- 
			(
			  annotate_lfu_in_goal(Inst0, Dead0, NI, ND ,
				Goal0, Goal), 
			  set__union(I0, NI, I), 
			  set__union(D0, ND, D)), 
		Goals0, 
		Goals, 
		Inst0, Inst, 
		Dead0, Dead).

	
:- end_module sr_lfu.
