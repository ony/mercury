/*
** Copyright (C) 2001 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
** The implementation of {det,semi,non}_{exit,fail}_port_code_{ac,sr}.
**
** The code including this file should define the following macros:
** 
** procname:			The name of the procedure whose body this is.
** fail_port or exit_port:	Says which field to increment and whether the
**				procedure is has detism det or failure.
** version_ac or version_sr:	Says whether the procedure whose body this is
**				is intended for use with or without
**				MR_USE_ACTIVATION_COUNTS.
**
** The code including this file should have the following variables in scope:
**
** MiddleCSD:			The id of the current csd.
** TopCSD:			The id of the parent's csd.
** OldOutermostActivationPtr:	The id of the outermost activation of the
**				current user procedure before the current call
**				to it. Needed only with version_sr.
*/

#ifdef MR_DEEP_PROFILING
{
	MR_CallSiteDynamic	*csd;
	MR_ProcStatic		*ps;

	MR_enter_instrumentation();

	csd = (MR_CallSiteDynamic *) MiddleCSD;
	MR_deep_assert(csd == MR_current_call_site_dynamic);

  #ifdef MR_DEEP_PROFILING_CALL_COUNTS
	/* increment exit/fail count */
    #if defined(fail_port)
	csd->MR_csd_own.MR_own_fails++;
    #elif defined(exit_port)
	csd->MR_csd_own.MR_own_exits++;
    #else
      #error "mercury_deep_leave_port_body.h: neither fail_port nor exit_port"
    #endif
  #endif

	MR_deep_assert(csd->MR_csd_callee_ptr != NULL);
	ps = csd->MR_csd_callee_ptr->MR_pd_proc_static;
	MR_deep_assert(ps != NULL);

  #if defined(version_ac)
    #ifdef MR_USE_ACTIVATION_COUNTS
	/* decrement activation count */
	ps->MR_ps_activation_count--;
	MR_deep_assert(ps->MR_ps_activation_count >= 0);
    #else
	MR_fatal_error(procname ": MR_USE_ACTIVATION_COUNTS not enabled");
    #endif
  #elif defined(version_sr)
    #ifndef MR_USE_ACTIVATION_COUNTS
	/* set outermost activation pointer */
	ps->MR_ps_outermost_activation_ptr =
		(MR_ProcDynamic *) OldOutermostActivationPtr;
    #else
	MR_fatal_error(procname ": MR_USE_ACTIVATION_COUNTS enabled");
    #endif
  #else
    #error "mercury_deep_leave_port_body.h: neither version_ac nor version_sr"
  #endif

	/* set current csd */
	MR_current_call_site_dynamic = (MR_CallSiteDynamic *) TopCSD;

	MR_leave_instrumentation();

  	/*
	** For fail_port code, the failure we should execute here
	** is handled by code inserted by the compiler.
	*/
}
#else
	MR_fatal_error(procname ": deep profiling not enabled");
#endif
