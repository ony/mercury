
/*
** Copyright (C) 1997 University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: print.h,v 1.1.2.1 1997-09-29 09:13:24 aet Exp $
*/


#ifndef MB_PRINT_H
#define	MB_PRINT_H

#include	<slist.h>

/*
** `depth' is the indentation depth (tabs from left margin)
*/
typedef void (*PrintFunction)(void *item, int depth);

void
MB_print_slist(MB_SList list, PrintFunction print, int depth);

void
MB_print_string(char *str, int depth);

void
MB_print_shared_object_dict(void);

void
MB_print_bytecode_module_dict(void);

void
MB_print_bytecode_proc_dict(void);

#endif	/* MB_PRINT_H */
