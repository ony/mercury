/*
** Copyright (C) 2001 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
** The implementation of non_redo_port_code_{ac,sr}.
**
** The code including this file should define the following macros:
** 
** procname:			The name of the procedure whose body this is.
** version_ac or version_sr:	Says whether the procedure whose body this is
**				is intended for use with or without
**				MR_USE_ACTIVATION_COUNTS.
**
** The code including this file should have the following variables in scope:
**
** MiddleCSD:			The id of the current csd.
** NewOutermostActivationPtr:	The id of the outermost activation of the
**				procedure being backtracked into after the
**				current call to it.
*/

#ifdef MR_DEEP_PROFILING
{
	MR_CallSiteDynamic	*csd;
	MR_ProcStatic		*ps;

	MR_enter_instrumentation();

	csd = (MR_CallSiteDynamic *) MiddleCSD;

	/* set current csd */
	MR_current_call_site_dynamic = csd;

  #ifdef MR_DEEP_PROFILING_CALL_COUNTS
	/* increment redo count */
	csd->MR_csd_own.MR_own_redos++;
  #endif

	MR_deep_assert(csd->MR_csd_callee_ptr != NULL);
	ps = csd->MR_csd_callee_ptr->MR_pd_proc_static;
	MR_deep_assert(ps != NULL);

  #if defined(version_ac)
    #ifdef MR_USE_ACTIVATION_COUNTS
	/* increment activation count */
	ps->MR_ps_activation_count++;
	ps->MR_ps_outermost_activation_ptr =
		(MR_ProcDynamic *) NewOutermostActivationPtr;
    #else
	MR_fatal_error(procname ": MR_USE_ACTIVATION_COUNTS not enabled");
    #endif
  #elif defined(version_sr)
    #ifndef MR_USE_ACTIVATION_COUNTS
	/* set outermost activation pointer */
	ps->MR_ps_outermost_activation_ptr =
		(MR_ProcDynamic *) NewOutermostActivationPtr;
    #else
	MR_fatal_error(procname ": MR_USE_ACTIVATION_COUNTS enabled");
    #endif
  #else
    #error "mercury_deep_leave_port_body.h: neither version_ac nor version_sr"
  #endif

	MR_leave_instrumentation();

  	/*
	** For fail_port code, the failure we should execute here
	** is handled by code inserted by the compiler.
	*/
}
#else
	MR_fatal_error(procname ": deep profiling not enabled");
#endif
