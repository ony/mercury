/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: util.c,v 1.8.4.1 1997-09-29 09:13:34 aet Exp $
*/


/* Imports */
#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<stdarg.h>
#include	<assert.h>

#include	"util.h"
#include	"mem.h"


/* Local declarations */

static char
rcs_id[]	= "$Id: util.c,v 1.8.4.1 1997-09-29 09:13:34 aet Exp $";

/* Implementation */

void 
MB_util_error(const char *fmt, ...)
{
        va_list arg_p;

        fprintf(stderr, "Error: ");
        va_start(arg_p, fmt);
        vfprintf(stderr, fmt, arg_p);
        va_end(argp);
        fprintf(stderr, "\n");
}

void 
MB_util_print(const char *fmt, ...)
{
        va_list arg_p;

        va_start(arg_p, fmt);
        vprintf(fmt, arg_p);
        va_end(argp);
        printf("\n");
}

void
MB_fatal(const char* message)
{
	MB_util_error(message);
	fprintf(stderr, "NOTE: The program is aborting. "
		 "Please keep the core file for diagnosis.\n");
	abort();

	return; /* not reached */
}

char*
MB_strdup(const char* str)
{
	int	size;
	char	*str2, *c_p;

	size = strlen(str) + 1;
	str2 = MB_malloc(size);
	for (c_p = str2; *str != '\0'; str++, c_p++)
	{
		*c_p = *str;
	}
	*c_p = '\0';

	return str2;
}

/*
** basename "a/b/c.exe" -> "c.exe"
*/
char *
MB_basename(char *str)
{
	/* XXX: STUB */
	return str;
}

/*
** XXX: This procedure is ugly, wastes space, and doesn't handle
** strings of form ".exe".
*/
char *
MB_drop_extension(const char *filename)
{
	int		i;
	const char	delimiter = '.';
	char		*basename;

	basename = MB_strdup(filename);

	for (i=0; '\0' != basename[i]; i++)
	{
		if (delimiter == basename[i])
		{
			basename[i] = '\0';
			break;
		}
	}

	return basename;
}

MB_Bool
MB_has_extension(const char *filename, const char* extension)
{
	int 	len;
	int	ext_len;

	assert(filename != NULL);
	assert(extension != NULL);

	len = strlen(filename);
	if (len <= strlen(extension)) {
		return FALSE;
	} else {
		if (strcmp(filename+len-strlen(extension),extension) == 0) {
			return TRUE;
		} else {
			return FALSE;
		}
	}
}
