
/*
** Copyright (C) 1997 University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: lineedit.c,v 1.1.2.1 1997-09-29 09:13:03 aet Exp $
*/

/* Imports */
#include	"template.h"

/* Exported definitions */

/* Local declarations */

static char
rcs_id[]	= "$Id: lineedit.c,v 1.1.2.1 1997-09-29 09:13:03 aet Exp $";

#ifndef USE_READLINE

#include	<stdio.h>
#include	<string.h>

#include	"mem.h"
#include	"lineedit.h"

/*
** XXX: this code is rubbish.
*/
char *
readline(char *prompt)
{

	static char	line_s[1000];
	char		*tmp;

	printf("%s", prompt);
	gets(line_s);

	tmp = MB_malloc(strlen(line_s) + 1);
	strcpy(tmp, line_s);
	return tmp;
}

void
add_history(char *line)
{
	/* do nothing */
	return;
}

#endif /* not USE_READLINE */

/* Implementation */

