
/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: slist.c,v 1.2.4.1 1997-09-29 09:13:26 aet Exp $
*/

/* Imports */
#include	<assert.h> /* for assert */

#include	"mem.h" /* for MB_malloc */
#include	"slist.h"

/* Exported definitions */

/* Local declarations */

static char
rcs_id[]	= "$Id: slist.c,v 1.2.4.1 1997-09-29 09:13:26 aet Exp $";

/* Implementation */

MB_SList
MB_slist_nil()
{
	return (MB_SList) NULL;
}

MB_Bool
MB_slist_null(MB_SList list)
{
	return NULL == list;
}

MB_SList
MB_slist_cons(void *head, MB_SList tail)
{
	MB_p_SList_Node	*tmp;

	tmp = (MB_SList) MB_malloc(sizeof(MB_p_SList_Node));

	tmp->p_head = head;
	tmp->p_tail = tail;

	return tmp;
}


void *
MB_slist_head(MB_SList list)
{
	assert(list != NULL); /* XXX */
	
	return list->p_head;
}

MB_SList
MB_slist_tail(MB_SList list)
{
	assert(list != NULL); /* XXX */

	return list->p_tail;
}


