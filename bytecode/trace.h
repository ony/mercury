
/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: trace.h,v 1.1.2.1 1997-10-24 09:46:23 aet Exp $
*/


#ifndef MB_TEMPLATE_H
#define	MB_TEMPLATE_H

#include	<stdio.h>

#include	"util.h"

extern FILE *
mb_tracefp;


#define MB_TRACE(func_name, message) \
	{ \
		if (MB_tracing(#func_name, __FILE__)) \
		{ \
			fprintf(mb_tracefp, "trace: %s#%d : %s : %s\n", \
				__FILE__, __LINE__, #func_name, #message); \
			fflush(mb_tracefp); \
		} \
	} while (0)

/*
** XXX: IMPORTANT: there must be -no- whitespace in the format_char argument
** since this may cause whitespace to intervene between the % and the
** format char in the format string.
** The format char probably should be changed to a format string for this
** reason.
*/
#define MB_TRACE2(func_name, format_char, value) \
	{ \
		if (MB_tracing(#func_name, __FILE__)) \
		{ \
			fprintf(mb_tracefp, "trace: %s#%d : %s : " \
				"%s = %" #format_char "\n", \
				__FILE__, __LINE__,  #func_name, \
				#value, value); \
			fflush(mb_tracefp); \
		} \
	} while(0)

MB_Bool
MB_tracing(const char *func_name, const char *file_name);

void
MB_trace_init(void);

#endif	/* MB_TEMPLATE_H */
