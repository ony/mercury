/*
** Copyright (C) 2001 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
** The implementation of {det,semi,non}_call_port_code_{ac,sr}.
**
** The code including this file should define the following macros:
** 
** procname:			The name of the procedure whose body this is.
** version_ac or version_sr:	Says whether the procedure whose body this is
**				is intended for use with or without
**				MR_USE_ACTIVATION_COUNTS.
** need_new_outermost:		Says whether we need to know the new value of
**				the outermost activation pointer. Should be
**				true only for non_call_port_code_*.
**
** The code including this file should have the following variables in scope:
**
** ProcStatic:			The proc_static of the procedure whose call
**				port we are at.
** MiddleCSD:			The id of the current csd.
** TopCSD:			The id of the parent's csd.
** OldOutermostActivationPtr:	The id of the outermost activation of the
**				current user procedure before the call.
**				Needed only with version_sr.
** NewOutermostActivationPtr:	The id of the outermost activation of the
**				current user procedure after the call.
**				Needed only with need_new_outermost.
*/

#ifdef MR_DEEP_PROFILING
{
	MR_CallSiteDynamic	*csd;
	MR_ProcStatic		*ps;

	MR_enter_instrumentation();

#ifdef	MR_DEEP_PROFILING_LOWLEVEL_DEBUG
	MR_print_deep_prof_vars(stdout);
#endif

	TopCSD = (MR_Word) MR_current_call_site_dynamic;
	MiddleCSD = (MR_Word) MR_next_call_site_dynamic;
	MR_current_call_site_dynamic = MR_next_call_site_dynamic;
	csd = MR_current_call_site_dynamic;
  #ifdef MR_DEEP_PROFILING_CALL_COUNTS
	csd->MR_csd_own.MR_own_calls++;
  #endif
	ps = (MR_ProcStatic *) ProcStatic;
  #ifdef version_sr
	OldOutermostActivationPtr =
		(MR_Word) ps->MR_ps_outermost_activation_ptr;
  #endif

  #if defined(version_ac)
    #ifdef MR_USE_ACTIVATION_COUNTS
	MR_deep_assert(ps->MR_ps_activation_count == 0
		|| ps->MR_ps_outermost_activation_ptr != NULL);

	if (csd->MR_csd_callee_ptr != NULL) {
		if (ps->MR_ps_activation_count == 0) {
			ps->MR_ps_outermost_activation_ptr =
				csd->MR_csd_callee_ptr;
		}
	} else if (ps->MR_ps_activation_count > 0) {
		MR_incr_activation_loads();
		csd->MR_csd_callee_ptr = ps->MR_ps_outermost_activation_ptr;
	} else {
		MR_ProcDynamic	*pd;

		MR_new_proc_dynamic(pd, ps);
		csd->MR_csd_callee_ptr = pd;
		ps->MR_ps_outermost_activation_ptr = pd;
	}

	ps->MR_ps_activation_count++;
    #else
	MR_fatal_error(procname ": MR_USE_ACTIVATION_COUNTS not enabled");
    #endif
  #elif defined(version_sr)
    #ifndef MR_USE_ACTIVATION_COUNTS
	if (csd->MR_csd_callee_ptr != NULL) {
		ps->MR_ps_outermost_activation_ptr = csd->MR_csd_callee_ptr;
	} else if (ps->MR_ps_outermost_activation_ptr != NULL) {
		csd->MR_csd_callee_ptr = ps->MR_ps_outermost_activation_ptr;
	} else {
		MR_ProcDynamic	*pd;

		MR_new_proc_dynamic(pd, ps);
		csd->MR_csd_callee_ptr = pd;
		ps->MR_ps_outermost_activation_ptr = csd->MR_csd_callee_ptr;
	}
    #else
	MR_fatal_error(procname ": MR_USE_ACTIVATION_COUNTS enabled");
    #endif
  #else
    #error "mercury_deep_call_port_body.h: neither version_ac nor version_sr"
  #endif

  #ifdef need_new_outermost
	NewOutermostActivationPtr =
		(MR_Word) ps->MR_ps_outermost_activation_ptr;
  #endif

	MR_leave_instrumentation();
}
#else
	MR_fatal_error(procname ": deep profiling not enabled");
#endif
