/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: machine.c,v 1.5.4.1 1997-09-29 09:13:06 aet Exp $
*/

/* Imports */
#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<assert.h>
#include	<dlfcn.h>

#include	"dict.h"

#include	"machine.h"

/* Exported definitions */

/* Local declarations */

static char
rcs_id[]	= "$Id: machine.c,v 1.5.4.1 1997-09-29 09:13:06 aet Exp $";

/*
** MB_shared_object_dict : filename -> handle
** MB_bytecode_module_dict : modulename -> info
** MB_bytecode_module_dict : mangled proc name -> code address in code area
*/
MB_Dict
MB_shared_object_dict,
MB_bytecode_module_dict,
MB_bytecode_proc_dict;

/*
** Machine for bytecode execution.
*/
MB_Machine
MB_bmachine;

static void
call(MB_CString module, MB_Bool is_function, MB_CString name, 
	MB_Short arity, MB_Proc_id proc_id);

/*
** XXX: code addresses should have type `Code*', which is equivalent
** to `void*' but (possibly!) makes things a little clearer.
*/
#if 0
static MB_Bool
proc_in_bytecode(MB_CString module, MB_CString pred,
	MB_Short arity, MB_Proc_id proc_id, void **code_addr_p);
#endif /* 0 */
static MB_Bool
proc_in_bytecode(MB_Proc_id proc_id, void **code_addr_p);

#if 0
static MB_Bool
proc_in_shared_objects(MB_CString module, MB_CString pred, 
	MB_Short arity, MB_Proc_id proc_id, void **code_addr_p);
#endif /* 0 */
static MB_Bool
proc_in_shared_objects(MB_Proc_id proc_id, void **code_addr_p);

static MB_CString
make_C_name(MB_CString module, MB_CString pred, 
	MB_Short arity, MB_Proc_id proc_id);

/* Implementation */

void
MB_machine_init(void)
{
	int	i;

	MB_dict_init((MB_KeyComparison) strcmp, &MB_shared_object_dict);
	MB_dict_init((MB_KeyComparison) strcmp, &MB_bytecode_module_dict);
	MB_dict_init((MB_KeyComparison) strcmp, &MB_bytecode_proc_dict);

	MB_bmachine.ip = NULL;
	
	return;
}

static void
call(MB_CString module, MB_Bool is_function, MB_CString name, 
	MB_Short arity, MB_Proc_id proc_id)
{
	/*
	** XXX: code_addr should have type Code_Addr?
	*/
	void	*code_addr;

	/*
	** XXX: Add `is_function' to proc_in_bytecode() and
	** proc_in_shared_objects().
	*/
	if (proc_in_bytecode(proc_id, &code_addr))
	{
		/* XXX */
	}
	else if (proc_in_shared_objects(proc_id, &code_addr))
	{
		/* XXX */
	}
	else
	{
		MB_util_error("called unknown %s procedure: "
				"%s.%s/%d#%d (%s)\n",
			(is_function ? "function" : "predicate"),
			module, name, arity, proc_id.mode_id, proc_id.string);
		exit(EXIT_FAILURE);
	}
}

/*
** Given a label and the address of a caller, return the address of
** the label.
*/
static int
label_to_address(MB_Short label, int caller_address)
{
	/*
	** XXX: STUB!
	*/
	return 0;
}


/*
** Is the given proc in the dictionary of bytecode procs? If so, what
** is the code address (index into the code area)?
*/
static MB_Bool
proc_in_bytecode(MB_Proc_id proc_id, void **code_addr_p)
{
	void	*code_p;

	if (MB_dict_lookup(proc_id.string, MB_bytecode_proc_dict, &code_p)) {
		*code_addr_p = code_p;
		return TRUE;
	} else {
		*code_addr_p = NULL;
		return FALSE;
	}
}


/*
** Is a proc in a shared module? If so, what is the code address?
*/
static MB_Bool
proc_in_shared_objects(MB_Proc_id proc_id, void **code_addr_p)
{

	void	*key, *key2, *val, *handle, *code_p;

	/*
	** Check through all handles in the shared_object_dict.
	*/
	if ( ! MB_dict_first_key(MB_shared_object_dict, &key))
	{
		*code_addr_p = NULL;
		return FALSE;
	} else {
		while(TRUE) {
			if ( ! MB_dict_lookup(key, MB_shared_object_dict, 
				&handle))
			{
				assert(FALSE); /* XXX */
			}

			/*
			** Lookup in this shobj.
			*/
			if ((code_p = dlsym(handle, proc_id.string))
				!= NULL)
			{
				*code_addr_p = code_p;
				return TRUE;
			} else {
				if ( ! MB_dict_next_key(
					MB_shared_object_dict,
					key, &key2)
				)
				{
					*code_addr_p = NULL;
					return FALSE;
				} else {
					key = key2;
				}
			}
		} /* end while(TRUE) */
	} /* end else */
} /* end proc_in_shared_objects() */

/*
** XXX: We no longer need make_C_name() since store the mangled proc
** names in the bytecode directly.
*/
#if 0
/*
** Given module.pred/arity#proc_id return a C string which is the name
** as found in the symbol table of the shared objects.
** Example:
**	mercury_builtin.unify/2#0
**	entry_mercury__mercury_builtin__unify_2_0
**
** XXX: The name mangling performed here should be exactly identical
** to that done in compiler/llds_out.name_mangle. We hack a version
** that copes only with the absolute simplest case.
**
** XXX: FIX THIS. HACK. 
**
** XXX: IMMEDIATE PROBLEM:
**	enter_pred does not store
**	a) whether is a predicate or a function
**	b) arity
**	We need this information!
*/
static MB_CString
make_C_name(MB_CString module, MB_CString pred, 
	MB_Short arity, MB_Proc_id proc_id
)
{
	
	/*
	** XXX: Yes, this code is utter shit. HACK.
	*/
	static char	c_name_s[200];
	static char	tmp_s[20];

	strcpy(c_name_s, "entry_mercury__");
	strcat(c_name_s, module);
	strcat(c_name_s, "__");
	strcat(c_name_s, pred);
	sprintf(tmp_s, "_%d_%d", arity, proc_id.mode_id);
	strcat(c_name_s, tmp_s);

	return c_name_s;
}

#endif /* 0 */

/*
** XXX: unit testing.
** Need to make this useful.
*/
#ifdef TEST_MACHINE

int
main(void)
{

	/*
	** Zeroth test
	*/
	MB_machine_init();

/*
** XXX: We no longer need make_C_name() since store the mangled proc
** names in the bytecode directly.
*/
#if 0
	/*
	** First test
	*/
	{
		int		i;
		MB_CString	c_name;
		struct {
			MB_CString	mod;
			MB_CString	pred;
			MB_Short	arity;
			MB_Proc_id	proc_id;
		}		preds[] =
			{
				/*
				** XXX: These test cases are very ill-chosen.
				** Get better ones when make_C_name() is
				** done properly.
				*/
				{"mercury_builtin","unify",2,0},
				{"byte","warm",6,0},
				{"funky","jammin",7,4},
				{"choice","wicked",8,6},
				{"ill","chill",9,2},
			};


		for (i=0; i < sizeof(preds)/sizeof(*preds); i++) 
		{
			c_name = make_C_name(preds[i].mod, 
				preds[i].pred, preds[i].arity, 
				preds[i].proc_id);
			fprintf(stderr, "make_C_name(%s.%s/%d#%d) = \"%s\"\n",
				preds[i].mod, preds[i].pred, 
				preds[i].arity, preds[i].proc_id, c_name);
		}
	} /* end first test */

#endif /* 0 */

	return EXIT_SUCCESS;
}

#endif /* TEST_MACHINE */


