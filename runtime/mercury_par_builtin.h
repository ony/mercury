/*
vim: ft=c ts=4 sw=4 et
*/
/*
** Copyright (C) 2009 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
** This module contains the definitions of the primitive operations we use to
** implement dependent AND-parallelism as C macros. The macros can be invoked
** either from the predicates representing the operations in par_builtin.m
** in the library directory, or from a foreign_proc version of those
** predicates inserted directly into compiler-generated code.
*/

#ifndef MERCURY_PAR_BUILTIN_H
#define MERCURY_PAR_BUILTIN_H

#include "mercury_context.h"
#include "mercury_thread.h"

#ifdef MR_THREAD_SAFE

    struct MR_Future_Struct {
        /* lock preventing concurrent accesses */
        MercuryLock     MR_fut_lock;

        /* whether this future has been signalled yet */
        int             MR_fut_signalled;

        /* linked list of all the contexts blocked on this future */
        MR_Context      *MR_fut_suspended;

        MR_Word         MR_fut_value;
    };

#else /* !MR_THREAD_SAFE */

    struct MR_Future_Struct {
        char dummy; /* ANSI C doesn't allow empty structs */
    };

#endif /* !MR_THREAD_SAFE */


/*
** The mutex needs to be destroyed when the future is garbage collected.
** For efficiency we might want to ignore this altogether, e.g. on Linux
** pthread_mutex_destroy() only checks that the mutex is unlocked.
**
** We initialize the value field only to prevent its previous value,
** which may point to an allocated block, keeping that block alive.
** Semantically, the value field is undefined at this point in time.
*/

#ifdef MR_CONSERVATIVE_GC
    extern  void    MR_finalize_future(void *obj, void *cd);

    #define MR_register_future_finalizer(Future)                            \
        do {                                                                \
            GC_REGISTER_FINALIZER(Future, MR_finalize_future,               \
                NULL, NULL, NULL);                                          \
            Future->MR_fut_value = 0;                                       \
        } while (0)
#else
    #define MR_register_future_finalizer(Future)                            \
        ((void) 0)
#endif

#ifdef MR_LL_PARALLEL_CONJ

    #define MR_par_builtin_new_future(Future)                               \
        do {                                                                \
            MR_Word fut_addr;                                               \
                                                                            \
            MR_incr_hp(fut_addr,                                            \
                MR_round_up(sizeof(MR_Future), sizeof(MR_Word)));           \
            Future = (MR_Future *) fut_addr;                                \
                                                                            \
            pthread_mutex_init(&(Future->MR_fut_lock), MR_MUTEX_ATTR);      \
            MR_register_future_finalizer(Future);                           \
                                                                            \
            Future->MR_fut_signalled = MR_FALSE;                            \
            Future->MR_fut_suspended = NULL;                                \
        } while (0)

    /*
    ** It would be nice if we could rely on an invariant such as
    ** `if MR_fut_signalled is true, then reading MR_fut_value is ok'
    ** even *without* wrapping up those two field accesses in the mutex,
    ** taking the mutex only when MR_fut_signalled is false. (We would
    ** then have to repeat the test of MR_fut_signalled, of course.)
    ** Unfortunately, memory systems today cannot be relied on to provide
    ** the required level of consistency; some don't have any way to ask
    ** for the necessary memory barrier.
    */

    MR_declare_entry(mercury__par_builtin__wait_resume);

    #define MR_par_builtin_wait_future(Future, Value)                       \
        do {                                                                \
            MR_LOCK(&(Future->MR_fut_lock), "future.wait");                 \
                                                                            \
            if (Future->MR_fut_signalled) {                                 \
                Value = Future->MR_fut_value;                               \
                MR_UNLOCK(&(Future->MR_fut_lock), "future.wait");           \
            } else {                                                        \
                MR_Context *ctxt;                                           \
                                                                            \
                /*                                                          \
                ** Put the address of the future at a fixed place known to  \
                ** mercury__par_builtin__wait_resume, to wit, the top of    \
                ** the stack.                                               \
                */                                                          \
                MR_incr_sp(1);                                              \
                MR_sv(1) = (MR_Word) Future;                                \
                                                                            \
                /*                                                          \
                ** Save this context and put it on the list of suspended    \
                ** contexts for this future.                                \
                */                                                          \
                ctxt = MR_ENGINE(MR_eng_this_context);                      \
                MR_save_context(ctxt);                                      \
                                                                            \
                ctxt->MR_ctxt_resume =                                      \
                    MR_ENTRY(mercury__par_builtin__wait_resume);            \
                ctxt->MR_ctxt_next = Future->MR_fut_suspended;              \
                Future->MR_fut_suspended = ctxt;                            \
                                                                            \
                MR_UNLOCK(&(Future->MR_fut_lock), "future.wait");           \
                                                                            \
                MR_ENGINE(MR_eng_this_context) = NULL;                      \
                MR_runnext();                                               \
            }                                                               \
        } while (0)

    #define MR_par_builtin_get_future(Future, Value)                        \
        do {                                                                \
            assert(Future->MR_fut_signalled);                               \
            Value = Future->MR_fut_value;                                   \
        } while (0)

    #define MR_par_builtin_signal_future(Future, Value)                     \
        do {                                                                \
            MR_Context *ctxt;                                               \
            MR_Context *next;                                               \
                                                                            \
            MR_LOCK(&(Future->MR_fut_lock), "future.signal");               \
                                                                            \
            /*                                                              \
            ** If the same future is passed twice to a procedure then it    \
            ** could be signalled twice, but the value must be the same.    \
            */                                                              \
            if (Future->MR_fut_signalled) {                                 \
                assert(Future->MR_fut_value == Value);                      \
            } else {                                                        \
                Future->MR_fut_signalled = MR_TRUE;                         \
                Future->MR_fut_value = Value;                               \
            }                                                               \
                                                                            \
            /* Schedule all the contexts blocked on this future. */         \
            ctxt = Future->MR_fut_suspended;                                \
            while (ctxt != NULL) {                                          \
                next = ctxt->MR_ctxt_next;                                  \
                MR_schedule_context(ctxt);  /* clobbers MR_ctxt_next */     \
                ctxt = next;                                                \
            }                                                               \
            Future->MR_fut_suspended = NULL;                                \
                                                                            \
            MR_UNLOCK(&(Future->MR_fut_lock), "future.signal");             \
        } while (0)

#else

    #define MR_par_builtin_new_future(Future)                               \
        do {                                                                \
            MR_fatal_error("internal error: "                               \
                "new_future should only be used "                           \
                "by lowlevel parallel grades");                             \
        } while (0)

    #define MR_par_builtin_wait_future(Future, Value)                       \
        do {                                                                \
            MR_fatal_error("internal error: "                               \
                "wait_future should only be used "                          \
                "by lowlevel parallel grades");                             \
        } while (0)

    #define MR_par_builtin_get_future(Future, Value)                        \
        do {                                                                \
            MR_fatal_error("internal error: "                               \
                "get_future should only be used "                           \
                "by lowlevel parallel grades");                             \
        } while (0)

    #define MR_par_builtin_signal_future(Future, Value)                     \
        do {                                                                \
            MR_fatal_error("internal error: "                               \
                "signal_future should only be used "                        \
                "by lowlevel parallel grades");                             \
        } while (0)

#endif

#endif /* not MERCURY_PAR_BUILTIN_H */