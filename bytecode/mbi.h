/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: mbi.h,v 1.7.4.1 1997-09-29 09:13:11 aet Exp $
*/

#ifndef	MB_MBI_H
#define	MB_MBI_H

/*
**	BC_call_mbi() simply calls BC_mbi_main() with no commandline
**	arguments. It is called from Mercury source.
*/
int
BC_call_mbi(void);

/*
** 	BC_mbi_main() is the entry point for the Mercury bytecode interpreter.
*/
int 
BC_mbi_main(int argc, char **argv);

#endif	/* ! MB_MBI_H */
