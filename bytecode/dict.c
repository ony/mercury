
/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: dict.c,v 1.3.4.1 1997-09-29 09:12:56 aet Exp $
*/

/* Imports */
#include	<stdlib.h>
#include	<unistd.h>
#include	<assert.h>

#include	"mem.h"
#include	"util.h"

#include	"dict.h"

/* Exported definitions */

/* Local declarations */

static char
rcs_id[]	= "$Id: dict.c,v 1.3.4.1 1997-09-29 09:12:56 aet Exp $";

static MB_p_Dict_Item *
insert(MB_KeyComparison cmp, const void *key, void *val, MB_p_Dict_Item *items);

static MB_Bool
lookup(MB_KeyComparison cmp, void *key, MB_p_Dict_Item *items, void **val_p);

static MB_p_Dict_Item *
delete(MB_KeyComparison cmp, void *key, MB_p_Dict_Item *items);

static MB_p_Dict_Item *
new_item_p(const void *key, void *val, MB_p_Dict_Item *next);

static MB_Bool
next_key(MB_KeyComparison cmp, MB_p_Dict_Item *items, 
	void *this_key, void **next_key_p);

/* Implementation */

/*
**	XXX: Yes, this implementation is hopelessly inefficient.
**	I'll replace it with a hash table when things are working.
*/

MB_Dict
MB_dict_new(MB_KeyComparison key_cmp)
{
	MB_Dict	*new_dict_p;

	new_dict_p = (MB_Dict*) MB_malloc(sizeof(MB_Dict));

	new_dict_p->p_key_cmp = key_cmp;
	new_dict_p->p_items = NULL;

	return *new_dict_p;
}

void
MB_dict_init(MB_KeyComparison key_cmp, MB_Dict *dict_p)
{
	dict_p->p_key_cmp = key_cmp;
	dict_p->p_items = NULL;
	return;
}

MB_Bool
MB_dict_is_empty(MB_Dict dict)
{
	return (dict.p_items == NULL);
}

void
MB_dict_insert(const void *key, void *val, MB_Dict *dict_p)
{
	assert(dict_p != NULL);
	assert(dict_p->p_key_cmp != NULL);

	dict_p->p_items = insert(dict_p->p_key_cmp, key, val, dict_p->p_items);
}

/*
** Insert items in ascending order sorted on keys.
*/
static MB_p_Dict_Item *
insert(MB_KeyComparison cmp, const void *key, void *val, MB_p_Dict_Item *items)
{
	if (items == NULL) {
		return new_item_p(key, val, NULL);
	} else if (cmp(key, items->p_key) < 0) {
		return new_item_p(key, val, items);
	} else if (cmp(key, items->p_key) > 0) {
		items->p_next = insert(cmp, key, val, items->p_next);
		return items;
	} else { /* keys are same */
		items->p_val = val;
		return items;
	}
}

MB_Bool
MB_dict_lookup(void *key, MB_Dict dict, void **val_p)
{
	assert (dict.p_key_cmp != NULL);
	return lookup(dict.p_key_cmp, key, dict.p_items, val_p);
}

static MB_Bool
lookup(MB_KeyComparison cmp, void *key, MB_p_Dict_Item *items, void **val_p)
{
	MB_p_Dict_Item	*cur;

	cur = items;

	while (TRUE) {
		if (cur == NULL) {
			return FALSE;
		} else if (cmp(cur->p_key,key) == 0) {
			*val_p = cur->p_val;
			return TRUE;
		} else {
			cur = cur->p_next;
		}
	}
}

void
MB_dict_delete(void *key, MB_Dict *dict_p)
{
	assert(dict_p != NULL);
	assert(dict_p->p_key_cmp != NULL);

	dict_p->p_items = delete(dict_p->p_key_cmp, key, dict_p->p_items);
	return;
}

static MB_p_Dict_Item *
delete(MB_KeyComparison cmp, void *key, MB_p_Dict_Item *items)
{
	if (items == NULL) {
		return NULL;
	} else if (cmp(key,items->p_key) == 0) {
		/*
		** XXX: Use Boehm GC to collect garbage node.
		*/
		return items->p_next;
	} else {
		items->p_next = delete(cmp, key, items->p_next);
		return items;
	}
}


MB_KeyComparison
MB_dict_key_compare(MB_Dict dict)
{
	return dict.p_key_cmp;
}

static MB_p_Dict_Item *
new_item_p(const void *key, void *val, MB_p_Dict_Item* next)
{
	MB_p_Dict_Item	*item_p;

	item_p = (MB_p_Dict_Item*) MB_malloc(sizeof(MB_p_Dict_Item));

	item_p->p_key = key;
	item_p->p_val = val;
	item_p->p_next = next;

	assert(item_p != NULL);
	return item_p;
}


MB_Bool
MB_dict_first_key(MB_Dict dict, void **first_key_p)
{
	if (dict.p_items == NULL)
	{
		*first_key_p = NULL;
		return FALSE;
	}
	else
	{
		*first_key_p = dict.p_items->p_key;
		return TRUE;
	}
}


MB_Bool
MB_dict_next_key(MB_Dict dict, void *this_key, void **next_key_p)
{
	if (dict.p_items == NULL)
	{
		next_key_p = NULL;
		return FALSE;
	}
	else
	{
		assert(dict.p_key_cmp != NULL);
		return next_key(dict.p_key_cmp, dict.p_items, 
			this_key, next_key_p);
	}
}

static MB_Bool
next_key(MB_KeyComparison cmp, MB_p_Dict_Item *items, 
	void *this_key, void **next_key_p
)
{
	if (items == NULL)
	{
		*next_key_p = NULL;
		return FALSE;
	}
	else if (cmp(items->p_key, this_key) < 0)
	{
		return next_key(cmp, items->p_next, this_key, next_key_p);
	}
	else if (cmp(items->p_key, this_key) == 0)
	{
		if (items->p_next == NULL)
		{
			*next_key_p = NULL;
			return FALSE;
		}
		else
		{
			*next_key_p = items->p_next->p_key;
			return TRUE;
		}
	}
	else /* items->p_key > this_key */
	{
		*next_key_p = NULL;
		return FALSE;
	}
}


#ifdef TEST_DICT

#include	<string.h>

int
main()
{
	char *
	strings[] = {"Twas", "brillig", "and", "the", 
		"slithy", "toves", "did", "gimble", NULL};
	char	**str_p;
	MB_Dict		dict;
	char		*val;
	char		*key;

	dict = MB_dict_new((MB_KeyComparison)strcmp);

	for (str_p = strings; *str_p != NULL; str_p++)
	{
		MB_dict_insert(*str_p, *str_p, &dict);
	}

	for (str_p = strings; *str_p != NULL; str_p++)
	{
		if (MB_dict_lookup((void*)*str_p, dict, (void**) &val))
		{
			printf("Lookup succeeded: key=\"%s\" val=\"%s\"\n",
				*str_p, val);
		}
		else
		{
			printf("Lookup failed for \"%s\"\n", *str_p);
		}
	}

	printf("\nITERATE THROUGH ALL KEYS\n\n");

	if ( ! MB_dict_first_key(dict, (void**) &key))
	{
		fprintf(stderr, "No first key!\n");
		exit(EXIT_FAILURE);
	}
	else
	{
		while (TRUE)
		{
			MB_dict_lookup((void*)key, dict, (void**) &val);
			printf("Lookup succeeded: key=\"%s\" val=\"%s\"\n",
				key, val);
			if ( ! MB_dict_next_key(dict, (void*) key,
				(void**) &key))
			{
				break;
			}
		}
	}

	return EXIT_SUCCESS;
}

#endif /* TEST_DICT */

