%-----------------------------------------------------------------------------%
% Copyright (C) 1996-2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module sr_lbu: implements the process of annotating each program point
% 		 with Local Backward Use (LBU) information. 
%	 	 (based on resume-points and possible aliasing)
% XXX this module is purely for testing the workings of the resume-point
% field. The LBU-pass is not intended as a separate compiler-pass. 
% XXX I'm not really convinced that LBU should be made alias-compatible
% at each program point for the Live-set to be correct by the end. 
%    1. I think the alias-compatibility was needed in our Prolog-prototype
%       because we derive the exact set of variables in BU for each 
%       predicate.. While here I'm pretty convinced that a fixpoint-
%      	computation for BU is a bit of an overkill. Deterministic and
%       semideterministic predicates do not need a global BU analysis
%	anyway. And for non-deterministic predicates it seems realistic
% 	to consider all of the headvariables as vars in BU (when 
%	backtracked to the point of the predicate, chances are all of
%    	the vars still will be needed somehow -- note that this is
% 	independent of the possibilities of reuse within such a nondet
%	predicate, cf the nondet mode of append, where headvar3 can be
%	safely reused for the generation of each new solution).
%    2. It is sufficient to know the simple Backward Use at each program
%       point, as it is anyhow combined with the alias information to 
%	obtain the set of live datastructures. 
% RESULT: we remove the alias-information threaded along this pass. 
% main author: nancy

:- module sr_lbu.

:- interface.

%-------------------------------------------------------------------%

:- import_module io.
:- import_module hlds_module. 

:- pred sr_lbu__lbu_pass( module_info, module_info, io__state, io__state).
:- mode sr_lbu__lbu_pass( in, out, di, uo) is det.

%-------------------------------------------------------------------%
%-------------------------------------------------------------------%

:- implementation. 

% library modules 
:- import_module list,map, bool, set, varset.
:- import_module string.
:- import_module std_util, require.

% mercury-compiler modules
:- import_module globals, options.
:- import_module hlds_pred. 
:- import_module passes_aux.
:- import_module hlds_goal.
:- import_module prog_data.

:- import_module sr_live.

% temporary inclusion
:- import_module sr_reuse.

sr_lbu__lbu_pass( HLDSin , HLDSout) --> 
	% get all the predicate id's 
	{ hlds_module__module_info_predids( HLDSin, ALL_PRED_IDS ) },
	% get all the id's of special predicates
	{ hlds_module__module_info_get_special_pred_map( HLDSin, SPEC_MAP) },
	{ map__values( SPEC_MAP, SPEC_PRED_IDS) }, 
	% remove the special pred_ids from the set of pred_ids
	{ list__delete_elems( ALL_PRED_IDS, SPEC_PRED_IDS, PRED_IDS0) },
	% filter out the predids of predicates not defined in this 
	% module 
	{ list__filter( 
		pred_defined_in_this_module(HLDSin),
		PRED_IDS0, PRED_IDS ) },

	list__foldl2( annotate_lbu_in_pred, PRED_IDS, HLDSin, HLDSout ).

:- pred pred_defined_in_this_module(module_info, pred_id).
:- mode pred_defined_in_this_module(in,in) is semidet.

pred_defined_in_this_module(HLDS,ID):-
	not(hlds_module__pred_not_defined_in_this_module(HLDS,ID)).

:- pred annotate_lbu_in_pred(pred_id, module_info, module_info, io__state,
		io__state).
:- mode annotate_lbu_in_pred(in,in,out,di,uo) is det.

annotate_lbu_in_pred( PRED_ID, HLDSin, HLDSout ) --> 
	{ hlds_module__module_info_pred_info( HLDSin, PRED_ID, PredInfo) }, 
	passes_aux__write_pred_progress_message(
			"% LBU-annotating ", 
			PRED_ID, 
			HLDSin), 

	% fetching the procids
	{ pred_info_procids(PredInfo, PROC_IDS) },
	
	% handling all procids
	{ list__foldl( annotate_lbu_in_proc(HLDSin, PRED_ID), 
			PROC_IDS, PredInfo, NewPredInfo) } ,

	% and updating the module_info with the new predinfo-state. 
	{ module_info_set_pred_info( HLDSin, PRED_ID, NewPredInfo, 
			HLDSout) }.


:- pred annotate_lbu_in_proc( module_info, pred_id, proc_id, 
		pred_info, pred_info ).
:- mode annotate_lbu_in_proc( in, in, in, in, out) is det.

annotate_lbu_in_proc( HLDS, _PRED_ID, PROC_ID, PredInfo0, 
		PredInfo) :- 
	pred_info_procedures( PredInfo0, Procedures0 )  , 
	map__lookup(Procedures0, PROC_ID, ProcInfo0 )  , 
	proc_info_goal(ProcInfo0, Goal0),

	% extra info to be caried around for each program point: 
	% 	LBU at previous point
	%	Aliases at previous point 
	% output after each specific goal:
	%	new LBU set, 
	% 	new Alias set

	set__init(Lbu0), 
	annotate_lbu_in_goal( HLDS, ProcInfo0, 
				Lbu0, _Lbu, Goal0, Goal), 

	proc_info_set_goal(ProcInfo0, Goal, ProcInfo) ,
	map__det_update(Procedures0, PROC_ID, ProcInfo, Procedures) ,
	pred_info_set_procedures( PredInfo0, Procedures, PredInfo) .

:- pred annotate_lbu_in_goal(module_info, proc_info, 
			set(prog_var), set(prog_var), 
			hlds_goal, hlds_goal).
:- mode annotate_lbu_in_goal(in, in, in, out, in, out) is det.

annotate_lbu_in_goal(HLDS, ProcInfo, 
		Lbu0, Lbu, TopGoal0, TopGoal):-

	% incorporate the fresh resume_vars into the Lbu-set
	TopGoal0 = Expr0 - Info0,
	info_get_backtrack_vars(Info0, RESUME_VARS), 
	set__union(Lbu0, RESUME_VARS, Lbu_01),
	(
		%%%%%%%%%%%%%%%%%%%
		% (1) conjunction %
		%%%%%%%%%%%%%%%%%%%
		Expr0 = conj(Goals0)
	->
		annotate_lbu_in_conj(HLDS, ProcInfo, Lbu_01,  
				Lbu, 
				Goals0, Goals), 
		Expr = conj(Goals) ,
		Info = Info0
	;
		%%%%%%%%%%%%
		% (2) call %
		%%%%%%%%%%%%
		Expr0 = call(_,_, CallVars, _, _, _)
	-> 
		% and now for the LBU
		goal_info_get_determinism(Info0, Det),
		(
			determinism_is_nondet(Det)
		->
			% if the call is nondeterministic, all 
			% actual vars are taken to be in Local Backward Use.
			set__list_to_set(CallVars,CallVars_set),	
			set__union(CallVars_set, Lbu_01, Lbu)
		;
			Lbu = Lbu_01
		),
		Expr = Expr0,
		Info = Info0
	;
		% (3) switch
		Expr0 = switch(A,B,Cases0,SM)
	->
		annotate_lbu_in_switch(HLDS, ProcInfo, 
				Lbu_01, Lbu,  
				Cases0, Cases), 
		Expr = switch(A,B,Cases,SM),
		Info = Info0
	;
		%%%%%%%%%%%%%
		% (4) unify %
		%%%%%%%%%%%%%
		Expr0 = unify(_,_,_,_,_)
	->
		% Lbu
		Lbu = Lbu_01, 
		Expr = Expr0,
		Info = Info0
	;
		%%%%%%%%%%%%
		% (5) disj %
		%%%%%%%%%%%%
		Expr0 = disj(Goals0, SM)
	->
		annotate_lbu_in_disj(HLDS, ProcInfo, Lbu_01,  
				Lbu, Goals0, Goals),
		Expr = disj(Goals, SM),
		Info = Info0
	;
		%%%%%%%%%%%%%%%%%%%%
		% (6) if_then_else %
		%%%%%%%%%%%%%%%%%%%%
		Expr0 = if_then_else( Vars, Cond0, Then0, Else0, SM)
	->
			% annotating the condition
			% starting from Lbu_01 (where resume_vars are
			% taken into account)
		annotate_lbu_in_goal( HLDS, ProcInfo, Lbu_01, 
				_LbuCond, Cond0, Cond),
			% when annotating the then-part, 
			% the lbu used for it may not contain the
			% resume-vars due to the else part. 	
			% trick: to calculate the Lbu0Then, we set
			% resume-point of the condition to no_resume_point.
		Cond0 = CondGoal0 - CondInfo0,
		goal_info_set_resume_point(CondInfo0, no_resume_point, 
				InfoTmp),
		CondTmp = CondGoal0 - InfoTmp, 
		annotate_lbu_in_goal( HLDS, ProcInfo, Lbu_01,  
				Lbu0Then, CondTmp, _),
		annotate_lbu_in_goal( HLDS, ProcInfo, Lbu0Then,  
				LbuThen, Then0, Then),
		annotate_lbu_in_goal( HLDS, ProcInfo, Lbu_01, 
				LbuElse, Else0, Else),
		set__union(LbuThen, LbuElse, Lbu),
		Expr = if_then_else( Vars, Cond, Then, Else, SM),
		Info = Info0
	;
		%%%%%%%%%%%
		% (7) not %
		%%%%%%%%%%%
		Expr0 = not(Goal0)
		% handled as if(Goal0) then fail else true
	->
		annotate_lbu_in_goal( HLDS, ProcInfo, Lbu_01, 
				Lbu, Goal0, Goal),
		% in the if_then_else context as above this would be:
		% Lbu = union(LbuThen, LbuElse),
		% LbuThen = Lbu0Then, 
		% LbuElse = Lbu_01,
		% Lbu0Then = Lbu_01 + Lbu due to non-determinism of Goal0 +
		%	resume-vars of not. ?
		% XXX to be double-checked!!!
		Expr = not(Goal),
		Info = Info0
	;
		%%%%%%%%%%%%
		% (8) some %
		%%%%%%%%%%%%
		Expr0 = some( Vars, CR, Goal0 )
	->
		annotate_lbu_in_goal( HLDS, ProcInfo, Lbu_01,  
				Lbu, Goal0, Goal),
		Expr = some( Vars, CR, Goal ),
		Info = Info0
	;
		%%%%%%%%%%%%%%%%%%%%%%%
		% (9)  generic_call   %
		% (10) pragma_c_code  %
		% (11) par_conj       %
		% (12) bi_implication %
		%%%%%%%%%%%%%%%%%%%%%%%
		Lbu = Lbu0, 
		Expr = Expr0,
		Info = Info0
	),
	goal_info_set_lbu(Info, Lbu, Info_new), 
	TopGoal = Expr - Info_new. 	

:- pred annotate_lbu_in_conj( module_info, proc_info, set(prog_var),  
			set(prog_var), 
			list(hlds_goal), list(hlds_goal)). 
:- mode annotate_lbu_in_conj(in, in, in, out, in, out) is det.

annotate_lbu_in_conj( HLDS, ProcInfo, Lbu0,  
				Lbu, Goals0, Goals) :- 
	list__map_foldl(
		pred( Goal0::in, Goal::out, 
		      L0::in, L::out ) is det :-
			( annotate_lbu_in_goal( HLDS, ProcInfo, L0,  
					L, Goal0, Goal) ),
		Goals0, Goals, 
		Lbu0, Lbu).

:- pred annotate_lbu_in_switch( module_info, proc_info, 
			set(prog_var), 
			set(prog_var), 
			list(case), list(case)).
:- mode annotate_lbu_in_switch( in, in, in, out, in, out) is det.

annotate_lbu_in_switch( HLDS, ProcInfo, Lbu0, Lbu, 
			Cases0, Cases) :- 
	list__map_foldl(
		pred( Case0::in, Case::out, 
		      L0::in, L::out) is det :-
			( 
			Case0 = case(CONS,Goal0), 
			annotate_lbu_in_goal( HLDS, ProcInfo, Lbu0, 
					Lnew, Goal0, Goal),
			Case  = case(CONS,Goal),
			set__union( L0, Lnew, L )
			),
		Cases0, Cases, 
		Lbu0, Lbu).

:- pred annotate_lbu_in_disj( module_info, proc_info, 
			set(prog_var), 
			set(prog_var), 
			list(hlds_goal), list(hlds_goal)).
:- mode annotate_lbu_in_disj( in, in, in, out, in, out) is det.

annotate_lbu_in_disj( HLDS, ProcInfo, Lbu0, Lbu, 
			Goals0, Goals) :- 
	list__map_foldl(
		pred( Goal0::in, Goal::out, 
		      L0::in, L::out ) is det :-
			( 
			annotate_lbu_in_goal( HLDS, ProcInfo, Lbu0, 
					Lnew, Goal0, Goal),
			set__union( L0, Lnew, L )
			),
		Goals0, Goals, 
		Lbu0, Lbu).

/*************************************************************************
:- pred map_foldl2(pred(T1,T2,T3,T3,T4,T4), list(T1), list(T2), T3, T3, 
			T4, T4).
:- mode map_foldl2(pred(in,out,in,out,in,out) is det, 
                   in, out, in, out, in, out) is det.

map_foldl2(P, L1, L, A1, A, B1, B):-
        (L1 = [X|Xs] ->
                P(X,Y,A1,A2,B1,B2),
                map_foldl2(P, Xs, Ys, A2, A, B2, B),
                L = [Y | Ys]
        ;
                L = [],
                A = A1,
                B = B1).
*************************************************************************/

:- pred determinism_is_nondet(prog_data__determinism).
:- mode determinism_is_nondet(in) is semidet.

determinism_is_nondet(nondet).
determinism_is_nondet(multidet).
determinism_is_nondet(cc_nondet).
determinism_is_nondet(cc_multidet).

:- pred info_get_backtrack_vars(hlds_goal_info, set(prog_var)).
:- mode info_get_backtrack_vars(in, out) is det.

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
