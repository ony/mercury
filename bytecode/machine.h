/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: machine.h,v 1.6.4.1 1997-09-29 09:13:08 aet Exp $
*/

#ifndef MB_MACHINE_H
#define	MB_MACHINE_H

#include	"conf.h"
#include	"mercury_types.h"	/* for Word */

#include	"bytecode.h"
#include	"dict.h"

/*
** XXX: How much of this stuff needs to be exported?
** It would seem more reasonable to keep the MB_Machine type
** local to this module. The interface of the disasm module is
** the ideal to aim for. 8^)
**
**	XXX: Currently we store full bloated bytecodes in the
**	code area (text segment). This is extremely inefficient.
**	We should alter design a stripped-down streamlined `machine
**	code'; that is a minimalist bytecode with all symbolic information
**	stripped out and and placed in tables (`data segment'), and all 
**	labels replaced with offsets into the text segment
*/


/*
** This is in analogy with the `Code' type from the Mercury runtime.
*/
typedef unsigned char
	MB_Code;

/*
** XXX: Should code_addr be an index into code[] in this module
** (and hence not be unique among different modules) or should it
** be a void* machine address?
** Currently we let it be an index.
**
** XXX: This name is -awful-. Choose a better one. `Code_Location'?
*/
typedef struct MB_Code_Addr_Module {
	Code		*code_addr;
	MB_CString	mod_name;
} MB_Code_Addr_Module;

/*
** XXX: The code area for each module is currently just an array of
** bytecodes. This is not the best data structure since:
**	- it imposes an arbitrary limit
**	- it wastes space
** Alternatives are:
**	- count the bytecodes and allocate exactly the right number
**	- when space is exhausted, realloc double the space.
** These approaches each have a downside.
*/
#define	MB_MAX_CODE		20000

typedef struct Bytecode_Module_Info {
	MB_CString	mod_name;
	MB_Dict		label_dict; /* label (MB_Short) -> Code_Addr */
	MB_Bytecode	code[MB_MAX_CODE]; /* bytecodes of the module */
	int		top; /* next free slot in code[] */

	/* XXX: The following can be added later. */
	#if 0
	MB_Dict		pred_dict; /* pred_name (MB_CString) -> Pred_Info* */
	#endif

} Bytecode_Module_Info;

#if 0
typedef struct Pred_Info {
	/*
	** XXX: code_address not really needed here.
	** XXX: what should type of code_address be?
	*/
	MB_Code		*code_address;
	MB_Dict		proc_dict; /* proc_id (MB_Proc_id) -> Proc_Info* */
} Pred_Info;

/*
** The information in a Proc_Info is exactly what is found in the
** enter_proc bytecode instruction.
** XXX: I don't know how much of this stuff we really need.
*/
typedef struct Proc_Info {
	/*
	** XXX: what should type of code_address be?
	*/
	MB_Code		*code_address;
	MB_Proc_id	proc_id;
	MB_Determinism	det;
	MB_Short	label_count;
	MB_Short	temp_count;
	MB_Short	list_length;
	MB_CString	*var_info_list;
} Proc_Info;
#endif /* 0 */

/*
** NOTE: If ip has a value of NULL, then it does not point to valid code.
*/
typedef struct MB_Machine_struct {
	MB_Code		*ip; /* Bytecode IP : address of next bytecode */
} MB_Machine;

/*
** The bytecode `machine'. It's not really much of a machine since
** almost all computation takes place inside the Mercury runtime, of which
** we use the registers, heaps and stacks.
*/
extern MB_Machine
MB_bmachine;


/*
** MB_shared_object_dict: MB_CString -> void*
** 	A dictionary whose keys are filenames of shared object 
** 	and whose values are handles for use by dlsym(3).
**
** MB_bytecode_module_dict: MB_CString -> MB_Bytecode_Module_Info*
**	A dictionary whose keys are module names of bytecode modules and
** 	whose values are the information table of that bytecode module.
**
** MB_bytecode_proc_dict: MB_CString -> MB_Code_Addr_Module*
**	A dictionary which maps from mangled proc name (as found in the
**	`call' and `enter_proc' instructions) to a code address,
**	which is the (machine) address of the first bytecode of the
**	procedure in the code[] area of the module.
*/
extern MB_Dict
MB_shared_object_dict,
MB_bytecode_module_dict,
MB_bytecode_proc_dict;

void
MB_machine_init(void);

#endif	/* MB_MACHINE_H */
