/*
** Copyright (C) 1997 University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: disasm.h,v 1.6.2.1 1997-07-11 09:25:09 crs Exp $
*/

#ifndef MB_DISASM_H
#define	MB_DISASM_H

#include	<stdio.h>	/* for FILE */


/*
 *	Disassemble a Mercury bytecode file.
 *
 *	`fp' points to the beginning of a Mercury bytecode file. 
 *	The disassembler output is directed to stdout.
 *	XXX: Maybe we should be able to specify the output file pointer?
 */
void
MB_disassemble(FILE* fp);

#endif	/* MB_DISASM_H */
