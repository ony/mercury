/*
** Copyright (C) 1993-1998,2000,2003-2009 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
** mercury_imp.h - defines the interface to the Mercury abstract machine.
**
** IMPORTANT: this must be the *first* header file that is #included.
** It must come before any system header files.  This is because on some
** systems, the system header files include inline functions, and this
** causes problems when using global register variables, as gcc requires
** global register variable declarations to precede any function definitions.
**
** This file just #includes most of the other Mercury runtime header files.
*/

#ifndef MERCURY_IMP_H
#define MERCURY_IMP_H

/*
** The #include of "mercury_conf.h" must come before the `#ifdef MR_USE_DLLS',
** because mercury_conf.h defines the MR_USE_DLLS macro.
*/

#include	"mercury_conf.h"

/*
** The following must come before any declarations of or use of
** global variables.  This is necessary to support DLLs on Windows.
** Note: `libmer_dll.h' is automatically generated by `Makefile.DLLs'.
*/

#ifdef MR_USE_DLLS
  #include "libmer_dll.h"
#endif

#include	"mercury_regs.h"	/* must come before system headers */

#ifdef MR_HIGHLEVEL_CODE
  #include	"mercury.h"
#endif

#include	"mercury_std.h"
#include	"mercury_debug.h"

#include	"mercury_types.h"
#include	"mercury_library_types.h"
#include	"mercury_file.h"
#include	"mercury_string.h"
#include	"mercury_float.h"
#include	"mercury_bootstrap.h"
#include	"mercury_stack_trace.h"
#include	"mercury_accurate_gc.h"
#include	"mercury_stack_layout.h"

#include	"mercury_tags.h"
#include	"mercury_goto.h"
#include	"mercury_calls.h"
#include	"mercury_ho_call.h"
#include	"mercury_engine.h"

#include	"mercury_memory.h"
#include	"mercury_heap.h"
#include	"mercury_stacks.h"
#include	"mercury_overflow.h"

#include	"mercury_label.h"
#include	"mercury_wrapper.h"
#include	"mercury_engine.h"
#include	"mercury_context.h"
#include	"mercury_thread.h"
#include	"mercury_type_info.h"
#include	"mercury_typeclass_info.h"
#include	"mercury_type_tables.h"
#ifdef MR_USE_TRAIL
#include	"mercury_trail.h"
#endif

#include	"mercury_prof.h"
#include	"mercury_misc.h"

#include	"mercury_region.h"
#include	"mercury_tabling.h"
#ifdef MR_USE_MINIMAL_MODEL_STACK_COPY
#include	"mercury_minimal_model.h"
#endif
#ifdef MR_USE_MINIMAL_MODEL_OWN_STACKS
#include	"mercury_mm_own_stacks.h"
#endif
#include	"mercury_par_builtin.h"

#include	"mercury_univ.h"
#include	"mercury_complexity.h"
#include	"mercury_term_size.h"

#include	"mercury_grade.h"

#endif /* not MERCURY_IMP_H */
