
/*
** Copyright (C) 1997 University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: print.c,v 1.1.2.1 1997-09-29 09:13:22 aet Exp $
*/

/* Imports */
#include	<stdlib.h>
#include	<stdio.h>
#include	<assert.h>

#include	"machine.h"
#include	"slist.h"
#include	"dict.h"
#include	"print.h"

/* Exported definitions */

/* Local declarations */



static char
rcs_id[]	= "$Id: print.c,v 1.1.2.1 1997-09-29 09:13:22 aet Exp $";


static void
print_dict(MB_Dict dict, PrintFunction print_key, 
	PrintFunction print_val, int indent);

static void
print_module_info(void* mod_info, int depth);

static void
print_code_addr_mod_p(MB_Code_Addr_Module *code_addr_mod_p, int depth);

static void
print_pointer(void *ptr, int depth);

static void
print_int(int num, int depth);

static void
indent(int depth);

/* Implementation */

void
MB_print_shared_object_dict()
{
	printf("shared_object_dict =\n");
	print_dict(MB_shared_object_dict, (PrintFunction)MB_print_string, 
		(PrintFunction)print_pointer, 1);
}

void
MB_print_bytecode_module_dict()
{
	printf("bytecode_module_dict =\n");
	print_dict(MB_bytecode_module_dict, (PrintFunction)MB_print_string,
		(PrintFunction)print_module_info, 1);
}

void
MB_print_bytecode_proc_dict()
{
	printf("bytecode_proc_dict =\n");
	print_dict(MB_bytecode_proc_dict, (PrintFunction)MB_print_string,
		(PrintFunction)print_code_addr_mod_p, 1);
}

static void
print_code_addr_mod_p(MB_Code_Addr_Module *code_addr_mod_p, int depth)
{
	indent(depth);
	printf("code_addr = 0x%p\n", code_addr_mod_p->code_addr);

	indent(depth);
	printf("mod_name = \"%s\"\n", code_addr_mod_p->mod_name);

	return;
}

static void
print_module_info(void* mod_info, int depth)
{
	indent(depth);
/*
	printf("mod_name = \"%s\"\n", 
	printf("\"print_module_info\" not yet implemented\n");
*/
}


void
MB_print_slist(MB_SList list, PrintFunction print, int depth)
{
	while ( ! MB_slist_null(list) )
	{
		print(MB_slist_head(list), depth);
		printf("\n");
		list = MB_slist_tail(list);
	}
}

static void
print_dict(MB_Dict dict, PrintFunction print_key, 
	PrintFunction print_val, int depth)
{
	void	*key, *next_key;
	void	*val;

	
	if ( ! MB_dict_first_key(dict, &key)) {
		return; /* No keys in dict */
	} else {
		while (TRUE) {
			print_key(key, depth);
			putchar('\n');
			if ( ! MB_dict_lookup(key, dict, &val)) {
				assert(FALSE);
			}
			print_val(val, depth+1);
			putchar('\n');

			if ( ! MB_dict_next_key(dict, key, &next_key)) {
				break;
			}

			key = next_key;
		}
	} /* else */
} /* print_dict */

void
MB_print_string(char *str, int depth)
{
	indent(depth);
	printf("\"%s\"", str);
}

static void
print_pointer(void *ptr, int depth)
{
	indent(depth);
	printf("%p", ptr);
}

static void
print_int(int num, int depth)
{
	indent(depth);
	printf("%d", num);
}

static void
indent(int depth)
{
	int	i;

	for (i=1; i <= depth; i++) {
		putchar('\t');
	}
}

