/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: disasm.h,v 1.8.4.1 1997-09-29 09:13:00 aet Exp $
*/

#ifndef MB_DISASM_H
#define	MB_DISASM_H

#include	<stdio.h>	/* for FILE */

#include	"bytecode.h"	/* for MB_Bytecode */


/*
 *	Disassemble a Mercury bytecode file.
 *
 *	`fp' points to the beginning of a Mercury bytecode file. 
 *	The disassembler output is directed to stdout.
 *	XXX: Maybe we should be able to specify the output file pointer?
 */
void
MB_disassemble(FILE* fp);

void
MB_print_bytecode(MB_Bytecode bytecode);

#endif	/* MB_DISASM_H */
