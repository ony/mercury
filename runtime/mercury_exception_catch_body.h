/*
** Copyright (C) 2001 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
** The internals of exception:builtin_catch.
**
** The versions of builtin_catch for the various determinisms should define
** the following macros:
** 
** proc_label
** proc_static
** model
** excp_handler
** handle_ticket_on_exit
**
** It should also define may_need_fail_action for the model_non versions.
**
** XXX Note that we call succeed_discard() to exit regardless of the determinism
** and (in the semidet case) of whether MR_r1 is true or false.  We just return the MR_r1 value
** back to our caller.
*/

/*
** Framevar(1) and possibly framevar(2) are used to save the inputs and/or
** outputs of the closure. The first framevar available for saving deep
** profiling information is framevar(3).
*/

#define	FIRST_DEEP_SLOT			3

/*
** Each procedure defines several local labels. The local label numbers are
** allocated as follows. Note that not all procedures use all of these labels.
*/

#define	CALL_PORT_RETURN_LABEL(pl)	MR_PASTE3(pl, _i, 1)
#define	CLOSURE_RETURN_LABEL(pl)	MR_PASTE3(pl, _i, 2)
#define	EXIT_PORT_RETURN_LABEL(pl)	MR_PASTE3(pl, _i, 3)
#define	REDO_REDOIP_LABEL(pl)		MR_PASTE3(pl, _i, 4)
#define	REDO_PORT_RETURN_LABEL(pl)	MR_PASTE3(pl, _i, 5)
#define	FAIL_REDOIP_LABEL(pl)		MR_PASTE3(pl, _i, 6)
#define	FAIL_PORT_RETURN_LABEL(pl)	MR_PASTE3(pl, _i, 7)

#if	defined(may_need_fail_action) && \
		(defined(MR_USE_TRAIL) || defined(MR_DEEP_PROFILING))
  #define excp_catch_redoip(pl)	MR_LABEL(FAIL_REDOIP_LABEL(pl))
#else
  #define excp_catch_redoip(pl)	MR_ENTRY(MR_do_fail);
#endif

/*****************************************************************************/

MR_define_entry(proc_label);

	/*
	** Create an exception handler entry on the nondet stack.
	** (Register MR_r3 holds the Handler closure.)
	*/
	MR_create_exception_handler("builtin_catch/3" model,
		excp_handler, MR_r3, excp_catch_redoip(proc_label));

#if	defined(may_need_fail_action) && defined(MR_DEEP_PROFILING)
	/*
	** Give the deep profiler control when execution backtracks into
	** the closure.
	*/
	MR_mktempframe(MR_LABEL(REDO_REDOIP_LABEL(proc_label)));
#endif

#ifdef	MR_DEEP_PROFILING
	MR_framevar(1) = MR_r2;
	MR_deep_non_call(proc_label, proc_static, FIRST_DEEP_SLOT,
		CALL_PORT_RETURN_LABEL(proc_label));
	MR_r1 = MR_framevar(1);	/* The Goal to call */
#else
	MR_r1 = MR_r2;		/* The Goal to call */
#endif
	MR_r2 = 0;		/* Zero additional input arguments */
	MR_r3 = 1;		/* One output argument */
	/*
	** Now call `Goal(Result)'.
	*/
	MR_call(MR_ENTRY(mercury__do_call_closure),
		MR_LABEL(CLOSURE_RETURN_LABEL(proc_label)),
		MR_ENTRY(proc_label));

MR_define_label(CLOSURE_RETURN_LABEL(proc_label));
	MR_update_prof_current_proc(MR_LABEL(proc_label));

#ifdef	MR_DEEP_PROFILING
	save_results();
	MR_deep_non_exit(proc_static, FIRST_DEEP_SLOT,
		EXIT_PORT_RETURN_LABEL(proc_label));
	restore_results();
#endif

#ifdef	MR_USE_TRAIL
	handle_ticket_on_exit();
#endif

	MR_succeed_discard();

#if	defined(may_need_fail_action) && defined(MR_DEEP_PROFILING)

MR_define_label(REDO_REDOIP_LABEL(proc_label));

	MR_deep_non_redo(proc_static, FIRST_DEEP_SLOT,
		REDO_PORT_RETURN_LABEL(proc_label));
	/* executes MR_fail() */
#endif

#if	defined(may_need_fail_action) && \
		(defined(MR_USE_TRAIL) || defined(MR_DEEP_PROFILING))

MR_define_label(FAIL_REDOIP_LABEL(proc_label));

#ifdef	MR_USE_TRAIL
	handle_ticket_on_fail();
#endif

#ifdef	MR_DEEP_PROFILING
	MR_deep_non_fail(proc_static, FIRST_DEEP_SLOT,
		FAIL_PORT_RETURN_LABEL(proc_label));
	/* executes MR_fail() */
#endif

#endif

#undef	FIRST_DEEP_SLOT

#undef	CALL_PORT_RETURN_LABEL
#undef	CLOSURE_RETURN_LABEL
#undef	EXIT_PORT_RETURN_LABEL
#undef	REDO_REDOIP_LABEL
#undef	REDO_PORT_RETURN_LABEL
#undef	FAIL_REDOIP_LABEL
#undef	FAIL_PORT_RETURN_LABEL

#undef	excp_catch_redoip
