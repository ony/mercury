%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module sr_lfu: implements the process of annotating each program point
%		 within a procedure definition with Local Forward Use 
% 	 	 (LFU) information. 
% main author: nancy

:- module structure_reuse__sr_lfu.

:- interface.

:- import_module hlds__hlds_pred. 

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
:- import_module std_util, require, io.

process_proc(ProcInfo0, ProcInfo) :-
	proc_info_goal(ProcInfo0, Goal0),

		% the set of variables initially instantiated 
	proc_info_liveness_info(ProcInfo0, Inst0), 
		% the set of variables initially dead (meaning 
		% syntactically dead)
	set__init(Dead0),
	
		% annotate each of the goals	
	annotate_lfu_in_goal(Goal0, Goal1, Inst0, Inst, Dead0, Dead), 
	
	set__difference(Inst, Dead, LFU),
	Goal1 = Expr1 - Info1, 
	goal_info_set_lfu(LFU, Info1, Info), 
	Goal = Expr1 - Info, 

	% XXX Global use is never being used, and I wouldn't see why it would
	% be. Anyway, if the local forward use depending on the liveness
	% (liveness.m) information is correct, then the LFU of the top-level
	% goal should be identical of what was used as the "global use". 
	% compute global use: global use = intersect(LFU, headvars)
	%% proc_info_headvars(ProcInfo01, HeadVars), 
	%% set__list_to_set(HeadVars, HeadVarsSet),
	%% set__intersect(LFU, HeadVarsSet, GlobalUse),

	% We update the latest procinfo, as the information derived
	% by the liveness pass is still needed (resume-point used
	% by the lbu-pass). 

	%% proc_info_set_global_use(ProcInfo01, GlobalUse, ProcInfo02),
	proc_info_set_goal(ProcInfo0, Goal, ProcInfo).


	% annotate_lfu_in_goal(InstantiatedVars0, DiedVars0, 
	%		       InstantiatedVars, DiedVars, Goalin, Goalout).
:- pred annotate_lfu_in_goal(hlds_goal::in, hlds_goal::out,
		set(prog_var)::in, set(prog_var)::out, 
		set(prog_var)::in, set(prog_var)::out) is det.

annotate_lfu_in_goal(!Goal, !Inst, !Dead) :- 
	!.Goal = Expr0 - Info0,
	(
		goal_is_atomic(Expr0)
	->
		calculateInstDead(Info0, !Inst, !Dead), 
		set__difference(!.Inst, !.Dead, LFU),
		goal_info_set_lfu(LFU, Info0, Info),
		!:Goal = Expr0 - Info
	;
		annotate_lfu_in_composite_goal(!Goal, !Inst, !Dead)
	).


	% Update the set of instantiated and dead variables. 
	% calculateInstDead(info, instantiatedvars0, instantiatedvars, 	
	%		deadvars0, deadvars)
:- pred calculateInstDead(hlds_goal_info::in, set(prog_var)::in, 
		set(prog_var)::out,
		set(prog_var)::in, set(prog_var)::out) is det.

calculateInstDead(Info, !Inst, !Dead) :- 
	% Inst = Inst0 + birth-set
	% Dead = Dead0 + death-set 
	goal_info_get_pre_births(Info, PreBirths), 
	goal_info_get_post_births(Info, PostBirths), 
	goal_info_get_post_deaths(Info, PostDeaths),
	goal_info_get_pre_deaths(Info, PreDeaths), 

	!:Inst = set__union_list([PreBirths, PostBirths, !.Inst]),
	!:Dead = set__union_list([PreDeaths, PostDeaths, !.Dead]).

:- pred annotate_lfu_in_composite_goal(hlds_goal::in, hlds_goal::out,
		set(prog_var)::in, set(prog_var)::out, 
		set(prog_var)::in, set(prog_var)::out) is det.

annotate_lfu_in_composite_goal(!TopGoal, !Inst, !Dead) :- 
	!.TopGoal = Expr0 - Info0,
	(
		Expr0 = conj(Goals0)
	->
		annotate_lfu_in_conj(Goals0, Goals, !Inst, !Dead),
		Expr = conj(Goals)
	;
		Expr0 = switch(A,B,Cases0)
	->
		annotate_lfu_in_cases(Cases0, Cases, !Inst, !Dead),
		Expr = switch(A,B,Cases)
	;
		Expr0 = disj(Disj0)
	->
		annotate_lfu_in_disjs(Disj0, Disj, !Inst, !Dead),
		Expr = disj(Disj)
	;
		Expr0 = not(Goal0)
	->
		annotate_lfu_in_goal(Goal0, Goal, !Inst, !Dead),
		Expr = not(Goal)
	;
		Expr0 = some(V, C, Goal0)
	->
		annotate_lfu_in_goal(Goal0, Goal, !Inst, !Dead),
		Expr = some(V,C,Goal)
	;
		Expr0 = if_then_else(V, Cond0, Then0, Else0)
	->
		Inst0 = !.Inst, 
		Dead0 = !.Dead, 
		annotate_lfu_in_goal(Cond0, Cond, !Inst, !Dead),
		annotate_lfu_in_goal(Then0, Then, !Inst, !Dead),
		annotate_lfu_in_goal(Else0, Else, Inst0, Inst1, Dead0, Dead1),
		set__union(Inst1, !Inst), 
		set__union(Dead1, !Dead), 
		Expr = if_then_else(V, Cond, Then, Else)
	;
		error("atomic call in annotate_lfu_in_goal_2"),
		Expr = Expr0
	),
	set__difference(!.Inst, !.Dead, LFU),
	goal_info_set_lfu(LFU, Info0, Info),
	!:TopGoal = Expr - Info. 

:- pred annotate_lfu_in_conj(list(hlds_goal)::in, list(hlds_goal)::out,
		set(prog_var)::in, set(prog_var)::out,
		set(prog_var)::in, set(prog_var)::out) is det.

annotate_lfu_in_conj(!Goals, !Inst, !Dead) :- 
	map_foldl2(annotate_lfu_in_goal, !Goals, !Inst, !Dead).

:- pred annotate_lfu_in_cases(list(case)::in, list(case)::out, 
		set(prog_var)::in, set(prog_var)::out, 
		set(prog_var)::in, set(prog_var)::out) is det.

annotate_lfu_in_cases(!Cases, !Inst, !Dead) :- 
	Inst0 = !.Inst, 
	Dead0 = !.Dead, 
	map_foldl2(
		pred(Case0::in, Case::out, I0::in, I::out, 
				D0::in, D::out) is det :- 
		   (
		   	Case0 = case(Cons, G0), 
			annotate_lfu_in_goal(G0, G, Inst0, NI, Dead0, ND), 
			Case = case(Cons, G), 
			set__union(I0, NI, I), 
			set__union(D0, ND, D)
		   ), 
		!Cases, !Inst, !Dead).

:- pred annotate_lfu_in_disjs(list(hlds_goal)::in, list(hlds_goal)::out,
		set(prog_var)::in, set(prog_var)::out,
	       	set(prog_var)::in, set(prog_var)::out) is det.

annotate_lfu_in_disjs(!Goals, !Inst, !Dead) :- 
	Inst0 = !.Inst, 
	Dead0 = !.Dead, 
	map_foldl2(
		pred(G0::in, G::out, I0::in, I::out, D0::in, D::out) is det :- 
		    (
			annotate_lfu_in_goal(G0, G, Inst0, NI, Dead0, ND),
			set__union(I0, NI, I), 
			set__union(D0, ND, D)
		    ), 
		!Goals, !Inst, !Dead). 
	
:- end_module sr_lfu.
