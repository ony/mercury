%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module sr_lbu: implements the process of annotating each program point
% 		 with Local Backward Use (LBU) information. 
%	 	 (based on resume-points and forward use information)
% main author: nancy
%
% We annotate each program point within a procedure definition with a set of
% variables which are in so-called Local Backward Use (LBU). A variable is said
% to be in LBU if it may be accessed upon backtracking. 
% This information is computed based on the backtrack-vars (i.e. the input
% variables of the alternative goals of a disjunction), and forward use
% information. 
%
% The full theory on how the LBU is propagated is detailed in Nancy Mazur's PhD
% thesis. We've implemented Instantiation 2 as to where non deterministic
% calls are concerned. 
% There are some slight variations as to the treatment of disjunctions,
% switches and if-then-elses. XXX This should be thoroughly checked!

:- module structure_reuse__sr_lbu.

:- interface.

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred. 

	% Precondition: the code must already be annotated with
	% LFU-information, and the resume-points must be filled. 
:- pred sr_lbu__process_proc(module_info::in,
		proc_info::in, proc_info::out) is det.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%

:- implementation. 

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_llds.
:- import_module hlds__instmap. 
:- import_module hlds__passes_aux.
:- import_module libs__globals.
:- import_module libs__options.
:- import_module parse_tree__prog_data.
:- import_module structure_reuse__sr_live.

:- import_module list,map, bool, set, varset.
:- import_module string.
:- import_module std_util, require.

sr_lbu__process_proc(HLDS, ProcInfo0, ProcInfo) :-
	proc_info_goal(ProcInfo0, Goal0),
	% extra info to be caried around for each program point: 
	% 	LBU at previous point
	% output after each specific goal:
	%	new LBU set, 
	set__init(Lbu0), 
	annotate_lbu_in_goal(HLDS, ProcInfo0, Goal0, Goal, Lbu0, _Lbu), 

	proc_info_set_goal(ProcInfo0, Goal, ProcInfo).

:- pred annotate_lbu_in_goal(module_info::in, proc_info::in, 
		hlds_goal::in, hlds_goal::out,
		set(prog_var)::in, set(prog_var)::out) is det.

annotate_lbu_in_goal(HLDS, ProcInfo, !TopGoal, !Lbu) :- 

	% incorporate the fresh resume_vars into the Lbu-set
	!.TopGoal = Expr0 - Info0,
	info_get_backtrack_vars(Info0, ResumeVars), 
	set__union(ResumeVars, !Lbu), 
	(
		%%%%%%%%%%%%%%%%%%%
		% (1) conjunction %
		%%%%%%%%%%%%%%%%%%%
		Expr0 = conj(Goals0),
		annotate_lbu_in_conj(HLDS, ProcInfo, 
				Goals0, Goals, !Lbu),
		Expr = conj(Goals)
	;
		%%%%%%%%%%%%
		% (2) call %
		%%%%%%%%%%%%
		Expr0 = call(_,_, _, _, _, _),
		goal_info_get_determinism(Info0, Det),
		(
			determinism_is_nondet(Det)
		->
			% Implementation of Instantiation 2 from Nancy's Phd.
			% In this instantation, a non deterministic procedure
			% call only adds the lfu-variables to the current set
			% of lbu-variables. Cf. Phd Nancy Mazur. 
			goal_info_get_lfu(Info0, Lfu), 
			set__union(Lfu, !Lbu)
		;
			true
		),
		Expr = Expr0
	;
		% (3) switch
		Expr0 = switch(A, B, Cases0),
		annotate_lbu_in_switch(HLDS, ProcInfo, Cases0, Cases, !Lbu),
		Expr = switch(A, B, Cases)
	;
		%%%%%%%%%%%%%
		% (4) unify %
		%%%%%%%%%%%%%
		Expr0 = unify(_, _, _, _, _),
		Expr = Expr0
	;
		%%%%%%%%%%%%
		% (5) disj %
		%%%%%%%%%%%%
		Expr0 = disj(Goals0),
		annotate_lbu_in_disj(HLDS, ProcInfo, Goals0, Goals, !Lbu),
		Expr = disj(Goals)
	;
		%%%%%%%%%%%%%%%%%%%%
		% (6) if_then_else %
		%%%%%%%%%%%%%%%%%%%%
		% XXX The implementation of this if-then-else is not in
		% accordance with the theory. Some more precision can be
		% obtained when the Condition of the if-then-else is a
		% deterministic goal (in which case, the Then-goal can be
		% analysed with the LBU with which the initial if-then-else in
		% analysed, instead of using the result of analysing the
		% condition. 
		Expr0 = if_then_else(Vars, Cond0, Then0, Else0),
		Lbu0 = !.Lbu, 
			% annotating the condition
			% starting from Lbu0 (where resume_vars are
			% taken into account)
		annotate_lbu_in_goal(HLDS, ProcInfo, Cond0, Cond, Lbu0, _),
			% when annotating the then-part, 
			% the lbu used for it may not contain the
			% resume-vars due to the else part. 	
			% trick: to calculate the Lbu0Then, we set
			% resume-point of the condition to no_resume_point.
		Cond0 = CondGoal0 - CondInfo0,
		goal_info_set_resume_point(CondInfo0, no_resume_point, 
				InfoTmp),
		CondTmp = CondGoal0 - InfoTmp, 
		annotate_lbu_in_goal(HLDS, ProcInfo, CondTmp, _, Lbu0, Lbu0T),
		annotate_lbu_in_goal(HLDS, ProcInfo, Then0, Then, 
				Lbu0T, LbuT), 
		annotate_lbu_in_goal(HLDS, ProcInfo, Else0, Else, 
				Lbu0, LbuE), 
		set__union(LbuT, LbuE, !:Lbu),
		Expr = if_then_else(Vars, Cond, Then, Else)
	;
		%%%%%%%%%%%
		% (7) not %
		%%%%%%%%%%%
		Expr0 = not(Goal0),
		% handled as if(Goal0) then fail else true
		Lbu0 = !.Lbu, 
		annotate_lbu_in_goal(HLDS, ProcInfo, Goal0, Goal, !.Lbu, _),
		% A not does not introduce any choice-points! Hence the
		% not itself is deterministic, and no new variables in LBU
		% are introduced. 
		!:Lbu = Lbu0,
		Expr = not(Goal)
	;
		%%%%%%%%%%%%
		% (8) some %
		%%%%%%%%%%%%
		Expr0 = some(Vars, CR, Goal0),
		annotate_lbu_in_goal(HLDS, ProcInfo, Goal0, Goal, !Lbu),
		Expr = some(Vars, CR, Goal)
	;
		Expr0 = generic_call(_, _, _, _), 
		Expr = Expr0
	;
		Expr0 = foreign_proc(_, _, _, _, _, _, _), 
		Expr = Expr0
	; 
		Expr0 = par_conj(_), 
		Expr = Expr0
	; 
		Expr0 = shorthand(_), 
		Expr = Expr0
	),
	goal_info_set_lbu(!.Lbu, Info0, Info), 
	!:TopGoal = Expr - Info. 	

:- pred annotate_lbu_in_conj(module_info::in, proc_info::in, 
		list(hlds_goal)::in, list(hlds_goal)::out,
		set(prog_var)::in,  set(prog_var)::out) is det.

annotate_lbu_in_conj(HLDS, ProcInfo, !Goals, !Lbu) :- 
	list__map_foldl( annotate_lbu_in_goal(HLDS, ProcInfo), !Goals, !Lbu). 

:- pred annotate_lbu_in_switch(module_info::in, proc_info::in, 
		list(case)::in, list(case)::out, 
		set(prog_var)::in, set(prog_var)::out) is det.

annotate_lbu_in_switch(HLDS, ProcInfo, !Cases, !Lbu) :- 
	Lbu0 = !.Lbu, 
	list__map_foldl(
		pred(Case0::in, Case::out, 
		      L0::in, L::out) is det :-
			(
			Case0 = case(Cons, G0), 
			annotate_lbu_in_goal(HLDS, ProcInfo, G0, G, Lbu0, LN),
			Case  = case(Cons, G),
			set__union(L0, LN, L)
			),
		!Cases, !Lbu).

:- pred annotate_lbu_in_disj(module_info::in, proc_info::in, 
		list(hlds_goal)::in, list(hlds_goal)::out,
		set(prog_var)::in, set(prog_var)::out) is det.

annotate_lbu_in_disj(HLDS, ProcInfo, !Goals, !Lbu) :- 
	Lbu0 = !.Lbu, 
	list__map_foldl(
		pred(G0::in, G::out, L0::in, L::out) is det :-
			(
			annotate_lbu_in_goal(HLDS, ProcInfo, G0, G, Lbu0, LN), 
			set__union(L0, LN, L)
			),
		!Goals, !Lbu). 

:- pred determinism_is_nondet(prog_data__determinism::in) is semidet.
determinism_is_nondet(nondet).
determinism_is_nondet(multidet).
determinism_is_nondet(cc_nondet).
determinism_is_nondet(cc_multidet).

:- pred info_get_backtrack_vars(hlds_goal_info::in, set(prog_var)::out) is det.
info_get_backtrack_vars(Info, Vars):- 
	goal_info_get_resume_point(Info, ResPoint), 
	(
		ResPoint = resume_point(ResVars, _)
	->
		Vars = ResVars
	;
		set__init(Vars)
	). 


:- end_module sr_lbu.
