/*
INIT mercury_sys_init_call
ENDINIT
*/
/*
** Copyright (C) 1995-2000 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

#define	MR_UNIFY_COMPARE_BY_CTOR_REP_SPEC_1
#define	MR_UNIFY_COMPARE_BY_CTOR_REP_SPEC_2

/*
** This module provides much of the functionality for doing higher order
** calls (with the rest provided by code generation of the generic_call
** HLDS construct), and most of the functionality for doing generic
** unifications and comparisons (with the rest provided by the
** compiler-generated unify, index and compare predicates).
*/

#include "mercury_imp.h"
#include "mercury_ho_call.h"

static	Word	MR_generic_compare(MR_TypeInfo type_info, Word x, Word y);
static	Word	MR_generic_unify(MR_TypeInfo type_info, Word x, Word y);

/*
** The called closure may contain only input arguments. The extra arguments
** provided by the higher-order call may be input or output, and may appear
** in any order.
**
** The input arguments to do_call_*_closure are the closure in r1,
** the number of additional input arguments in r2, the number of output
** arguments to expect in r3, and the additional input arguments themselves
** in r4, r5, etc. The output arguments are returned in registers r1, r2, etc
** for det and nondet calls or registers r2, r3, etc for semidet calls.
**
** The placement of the extra input arguments into r4, r5 etc is done by
** the code generator, as is the movement of the output arguments to their
** eventual destinations.
*/

	/*
	** Number of input arguments to do_call_*_closure,
	** r1 -> closure
	** r2 -> number of immediate input arguments.
	** r3 -> number of output arguments (unused).
	*/
#define MR_HO_CALL_INPUTS		3

	/*
	** Number of input arguments to do_call_*_class_method,
	** r1 -> typeclass info
	** r2 -> index of method in typeclass info
	** r3 -> number of immediate input arguments.
	** r4 -> number of output arguments (unused).
	*/
#define MR_CLASS_METHOD_CALL_INPUTS	4

/*
** These are the real implementations of higher order calls and method calls.
*/

Define_extern_entry(mercury__do_call_closure);
Define_extern_entry(mercury__do_call_class_method);

/*
** These are the real implementations of unify and compare.
*/

Define_extern_entry(mercury__unify_2_0);
Define_extern_entry(mercury__compare_3_0);
Define_extern_entry(mercury__compare_3_1);
Define_extern_entry(mercury__compare_3_2);
Define_extern_entry(mercury__compare_3_3);

#ifdef MR_PROFILE_DEEP
MR_MAKE_HO_CALL_SITE(genu_to_specu, mercury__unify_2_0, "runtime", 334);
MR_MAKE_SCC_ID(unify_scc_id, { }, { &genu_to_specu }, { });
MR_MAKE_PROC_LAYOUT(mercury__unify_2_0, MR_DETISM_SEMI, 0, 0,
			MR_PREDICATE, "builtin", "unify", 2, 0,
			unify_scc_id);

MR_MAKE_HO_CALL_SITE(genc_to_specc0, mercury__compare_3_0, "builtin", 738);
MR_MAKE_SCC_ID(compare_scc_id0, { }, { &genc_to_specc0 }, { });
MR_MAKE_PROC_LAYOUT(mercury__compare_3_0, MR_DETISM_DET, 0, 0,
			MR_PREDICATE, "builtin", "compare", 3, 0,
			compare_scc_id0);

MR_MAKE_HO_CALL_SITE(genc_to_specc1, mercury__compare_3_1, "builtin", 738);
MR_MAKE_SCC_ID(compare_scc_id1, { }, { &genc_to_specc1 }, { });
MR_MAKE_PROC_LAYOUT(mercury__compare_3_1, MR_DETISM_DET, 0, 0,
			MR_PREDICATE, "builtin", "compare", 3, 1,
			compare_scc_id1);

MR_MAKE_HO_CALL_SITE(genc_to_specc2, mercury__compare_3_2, "builtin", 738);
MR_MAKE_SCC_ID(compare_scc_id2, { }, { &genc_to_specc2 }, { });
MR_MAKE_PROC_LAYOUT(mercury__compare_3_2, MR_DETISM_DET, 0, 0,
			MR_PREDICATE, "builtin", "compare", 3, 2,
			compare_scc_id2);

MR_MAKE_HO_CALL_SITE(genc_to_specc3, mercury__compare_3_3, "builtin", 738);
MR_MAKE_SCC_ID(compare_scc_id3, { }, { &genc_to_specc3 }, { });
MR_MAKE_PROC_LAYOUT(mercury__compare_3_3, MR_DETISM_DET, 0, 0,
			MR_PREDICATE, "builtin", "compare", 3, 3,
			compare_scc_id3);
#endif

BEGIN_MODULE(call_module)
	init_entry_ai(mercury__do_call_closure);
	init_entry_ai(mercury__do_call_class_method);
	init_entry_ai(mercury__unify_2_0);
	init_entry_ai(mercury__compare_3_0);
	init_entry_ai(mercury__compare_3_1);
	init_entry_ai(mercury__compare_3_2);
	init_entry_ai(mercury__compare_3_3);
BEGIN_CODE

Define_entry(mercury__do_call_closure);
{
	MR_Closure	*closure;
	int		num_extra_args;	/* # of args provided by our caller */
	int		num_hidden_args;/* # of args hidden in the closure  */
	int		i;

	closure = (MR_Closure *) r1;
	num_extra_args = r2;
	num_hidden_args = closure->MR_closure_num_hidden_args;

	save_registers();

	if (num_hidden_args < MR_HO_CALL_INPUTS) {
		/* copy to the left, from the left */
		for (i = 1; i <= num_extra_args; i++) {
			virtual_reg(i + num_hidden_args) =
				virtual_reg(i + MR_HO_CALL_INPUTS);
		}
	} else if (num_hidden_args > MR_HO_CALL_INPUTS) {
		/* copy to the right, from the right */
		for (i = num_extra_args; i > 0; i--) {
			virtual_reg(i + num_hidden_args) =
				virtual_reg(i + MR_HO_CALL_INPUTS);
		}
	} /* else the new args are in the right place */

	for (i = 1; i <= num_hidden_args; i++) {
		virtual_reg(i) = closure->MR_closure_hidden_args(i);
	}

	restore_registers();

	tailcall(closure->MR_closure_code,
		LABEL(mercury__do_call_closure));
}

	/*
	** r1: the typeclass_info
	** r2: index of class method
	** r3: number of immediate input arguments
	** r4: number of output arguments
	** r5+:input args
	*/

Define_entry(mercury__do_call_class_method);
{
	Code 	*destination;
	int	num_in_args;
	int	num_extra_instance_args;
	int	i;

	destination = MR_typeclass_info_class_method(r1, r2);
	num_extra_instance_args = 
		(int) MR_typeclass_info_num_extra_instance_args(r1);

	num_in_args = r3; /* number of input args */

	save_registers();

	if (num_extra_instance_args < MR_CLASS_METHOD_CALL_INPUTS) {
		/* copy to the left, from the left */
		for (i = 1; i <= num_in_args; i++) {
			virtual_reg(i + num_extra_instance_args) =
				virtual_reg(i + MR_CLASS_METHOD_CALL_INPUTS);
		}
	} else if (num_extra_instance_args > MR_CLASS_METHOD_CALL_INPUTS) {
		/* copy to the right, from the right */
		for (i = num_in_args; i > 0; i--) {
			virtual_reg(i + num_extra_instance_args) =
				virtual_reg(i + MR_CLASS_METHOD_CALL_INPUTS);
		}
	} /* else the new args are in the right place */

	for (i = num_extra_instance_args; i > 0; i--) {
		virtual_reg(i) = 
			MR_typeclass_info_arg_typeclass_info(virtual_reg(1),i);
	}

	restore_registers();

	tailcall(destination, LABEL(mercury__do_call_class_method));
}

/*
** mercury__unify_2_0 is called as `unify(TypeInfo, X, Y)'
** in the mode `unify(in, in, in) is semidet'.
*/

Define_entry(mercury__unify_2_0);
{

#define	DECLARE_LOCALS							\
	MR_TypeCtorInfo	type_ctor_info;					\
	MR_TypeInfo	type_info;					\
	Word		x, y;						\
	Code		*saved_succip;

#define initialize()							\
	do {								\
		type_info = (MR_TypeInfo) r1;				\
		x = r2;							\
		y = r3;							\
		saved_succip = MR_succip;				\
	} while(0)

#define return_answer(answer)						\
	do {								\
		r1 = (answer);						\
		MR_succip = saved_succip;				\
		proceed();						\
	} while(0)

#ifndef MR_PROFILE_DEEP
#define	tailcall_user_pred()						\
	tailcall(type_ctor_info->unify_pred, LABEL(mercury__unify_2_0))
#else
#define	tailcall_user_pred()						\
{									\
	do {								\
		/*							\
		** When doing deep profiling, we need to		\
		** make a stack frame and treat the call		\
		** the way user HO calls get treated,			\
		** except that instead of using an MR_Closure		\
		** we use the data from the type_info.			\
		*/							\
		MR_incr_sp_push_msg(3, "runtime:unify/2");		\
		MR_stackvar(3) = (Word) MR_succip;			\
		MR_stackvar(2) = (Word) MR_SCC_INST(&unify_scc_id);	\
		MR_scc_from_here(&unify_scc_id);			\
		MR_stackvar(1) = (Word) MR_prof_current_proc;		\
		MR_prof_current_proc = MR_special_ho_call(0,		\
				type_ctor_info->unify_pred,		\
				type_ctor_info->unify_info);		\
									\
		noprof_call_localret(type_ctor_info->unify_pred,	\
			mercury__unify_2_0_i0);				\
	} while (0);							\
	Define_label(mercury__unify_2_0_i0);				\
	do {								\
		MR_prof_current_proc =					\
			(MR_ProcCallProfile *) MR_stackvar(1);		\
		MR_SET_SCC_INST(&unify_scc_id, MR_stackvar(2));		\
		MR_succip = (Code *) MR_stackvar(3);			\
		MR_decr_sp_pop_msg(3);					\
		proceed();						\
	} while(0);							\
}	
#endif

#define	start_label		unify_start
#define	call_user_code_label	call_unify_in_proc
#define	type_stat_struct	MR_type_stat_mer_unify
#define	attempt_msg		"attempt to unify "

#include "mercury_unify_compare_body.h"

#undef  DECLARE_LOCALS
#undef  initialize
#undef  return_answer
#undef	tailcall_user_pred
#undef  start_label
#undef	call_user_code_label
#undef  type_stat_struct
#undef  attempt_msg

}

/*
** mercury__compare_3_3 is called as `compare(TypeInfo, Result, X, Y)'
** in the mode `compare(in, out, in, in) is det'.
**
** (The additional entry points replace either or both "in"s with "ui"s.)
*/

Define_entry(mercury__compare_3_0);
#ifdef PROFILE_CALLS
{
	tailcall(ENTRY(mercury__compare_3_3), LABEL(mercury__compare_3_0));
}
#endif
Define_entry(mercury__compare_3_1);
#ifdef PROFILE_CALLS
{
	tailcall(ENTRY(mercury__compare_3_3), LABEL(mercury__compare_3_1));
}
#endif
Define_entry(mercury__compare_3_2);
#ifdef PROFILE_CALLS
{
	tailcall(ENTRY(mercury__compare_3_3), LABEL(mercury__compare_3_2));
}
#endif
Define_entry(mercury__compare_3_3);
{

#define	DECLARE_LOCALS							\
	MR_TypeCtorInfo	type_ctor_info;					\
	MR_TypeInfo	type_info;					\
	Word		x, y;						\
	Code		*saved_succip;

#define initialize()							\
	do {								\
		type_info = (MR_TypeInfo) r1;				\
		x = r2;							\
		y = r3;							\
		saved_succip = MR_succip;				\
	} while(0)

#define return_answer(answer)						\
	do {								\
		r1 = (answer);						\
		MR_succip = saved_succip;				\
		proceed();						\
	} while(0)

#ifndef MR_PROFILE_DEEP
#define	tailcall_user_pred()						\
	tailcall(type_ctor_info->compare_pred, LABEL(mercury__compare_3_3))
#else
#define	tailcall_user_pred()						\
{									\
	do {								\
		/*							\
		** When doing deep profiling, we need to		\
		** make a stack frame and treat the call		\
		** the way user HO calls get treated,			\
		** except that instead of using an MR_Closure		\
		** we use the data from the type_info.			\
		*/							\
		MR_incr_sp_push_msg(3, "runtime:compare/3");		\
		MR_stackvar(3) = (Word) MR_succip;			\
		MR_stackvar(2) = (Word) MR_SCC_INST(&compare_scc_id0);	\
		MR_scc_from_here(&compare_scc_id0);			\
		MR_stackvar(1) = (Word) MR_prof_current_proc;		\
		MR_prof_current_proc = MR_special_ho_call(0,		\
				type_ctor_info->compare_pred,		\
				type_ctor_info->compare_info);		\
									\
		noprof_call_localret(type_ctor_info->compare_pred,	\
			mercury__compare_3_0_i0);			\
									\
	} while(0);							\
	Define_label(mercury__compare_3_0_i0);				\
	do {								\
		MR_prof_current_proc =					\
			(MR_ProcCallProfile *) MR_stackvar(1);		\
		MR_SET_SCC_INST(&compare_scc_id0, MR_stackvar(2));	\
		MR_succip = (Code *) MR_stackvar(3);			\
		MR_decr_sp_pop_msg(3);					\
		proceed();						\
	} while(0);							\
}
#endif

#define	start_label		compare_start
#define	call_user_code_label	call_compare_in_proc
#define	type_stat_struct	MR_type_stat_mer_compare
#define	attempt_msg		"attempt to compare "
#define	select_compare_code

#include "mercury_unify_compare_body.h"

#undef  DECLARE_LOCALS
#undef  initialize
#undef  return_answer
#undef	tailcall_user_pred
#undef  start_label
#undef	call_user_code_label
#undef  type_stat_struct
#undef  attempt_msg
#undef	select_compare_code

}
END_MODULE

static Word
MR_generic_unify(MR_TypeInfo type_info, Word x, Word y)
{

#define	DECLARE_LOCALS							\
	MR_TypeCtorInfo	type_ctor_info;

#define initialize()							\
	do {								\
		(void) 0; /* do nothing */				\
	} while(0)

#define return_answer(answer)						\
	return (answer)

#define	tailcall_user_pred()						\
	do {								\
		save_transient_registers();				\
		(void) MR_call_engine(type_ctor_info->unify_pred, FALSE);\
		restore_transient_registers();				\
		return (r1);						\
	} while (0)

#define	start_label		unify_func_start
#define	call_user_code_label	call_unify_in_func
#define	type_stat_struct	MR_type_stat_c_unify
#define	attempt_msg		"attempt to unify "

#include "mercury_unify_compare_body.h"

#undef  DECLARE_LOCALS
#undef  initialize
#undef  return_answer
#undef	tailcall_user_pred
#undef  start_label
#undef	call_user_code_label
#undef  type_stat_struct
#undef  attempt_msg
}

static Word
MR_generic_compare(MR_TypeInfo type_info, Word x, Word y)
{

#define	DECLARE_LOCALS							\
	MR_TypeCtorInfo	type_ctor_info;

#define initialize()							\
	do {								\
		(void) 0; /* do nothing */				\
	} while(0)

#define return_answer(answer)						\
	return (answer)

#define	tailcall_user_pred()						\
	do {								\
		save_transient_registers();				\
		(void) MR_call_engine(type_ctor_info->compare_pred, FALSE);\
		restore_transient_registers();				\
		return (r1);						\
	} while (0)

#define	start_label		compare_func_start
#define	call_user_code_label	call_compare_in_func
#define	type_stat_struct	MR_type_stat_c_compare
#define	attempt_msg		"attempt to compare "
#define	select_compare_code

#include "mercury_unify_compare_body.h"

#undef  DECLARE_LOCALS
#undef  initialize
#undef  return_answer
#undef	tailcall_user_pred
#undef  start_label
#undef	call_user_code_label
#undef  type_stat_struct
#undef  attempt_msg
#undef	select_compare_code
}

void mercury_sys_init_call(void); /* suppress gcc warning */
void mercury_sys_init_call(void) {
	call_module();
}
