/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: mbi.c,v 1.9.4.1 1997-09-29 09:13:10 aet Exp $
*/

/* Imports */

	/*
	** Interface to Mercury runtime must be included first.
	*/
#include	"imp.h"

#include	<stdlib.h>
#include	<stdio.h>
#include	<unistd.h>
#include	<getopt.h>
#include	<dlfcn.h>
#include	<assert.h>

#include	"std.h"
#include	"util.h"
#include	"mem.h"
#include	"mbi.h"
#include	"bytecode.h"
#include	"print.h"
#include	"dict.h"
#include	"machine.h"
#include	"lineedit.h"
#include	"disasm.h"
#include	"slist.h"


/* Exports */


/* Local declarations */

/*
**	XXX: Only a tiny set of these debugging commands will be implemented
**	at first. In fact, there are plenty of other useful commands
**	that have been omitted.
**	N.B. It is -not- our aim to imitate a Prolog or C debugger.
*/
typedef enum Command_Name {
	COMMAND_CALL,	/* call a predicate */
	COMMAND_CLEAR,
	COMMAND_CONT,
	COMMAND_DEBUG,
	COMMAND_DISASM,	/* disassemble bytecode in code area */
	COMMAND_ERROR,	/* erroneous command */
	COMMAND_EXIT,	/* exit */
	COMMAND_FAIL,
	COMMAND_HELP,	/* command help */
	COMMAND_LEASH,
	COMMAND_LIST,	/* list lines of source (or bytecode?) */
	COMMAND_LOAD, 	/* load modules (shared object or bytecode files) */
	COMMAND_MODULES, /* list loaded modules (.so and .mbc files) */
	COMMAND_NODEBUG,
	COMMAND_NONE,	/* no command entered */
	COMMAND_PRINT,
	COMMAND_PROC,	/* xxx: set current procedure --- awful name */
	COMMAND_RETRY,
	COMMAND_RUN,	/* run an i/o predicate such as main/2 */
	COMMAND_SET,	/* set depth|size|scope|... */
	COMMAND_SKIP,
	COMMAND_STEP,
	COMMAND_STOP_AT,
	COMMAND_STOP_IN,
	COMMAND_TESTXXX,
	COMMAND_TRACE,
	COMMAND_UNLOAD,
	COMMAND_USE,
	COMMAND_WHERE
} Command_Name;

typedef struct Command {
	Command_Name	name;
	MB_SList	args;
} Command;

static char
rcs_id[]	= "$Id: mbi.c,v 1.9.4.1 1997-09-29 09:13:10 aet Exp $";

static char*
program_name	= NULL;

/*
** XXX: This file extension differs from platform to platform.
** It should be set by configuration.
*/
static const char*
shared_obj_extension	= ".so";

static const char*
bytecode_file_extension= ".mbc";

/*
** XXX: This `command_help' is way ugly. There must be a better way of
** doing it. It's also not complete! 8^)
*/
static struct {
	Command_Name	command_name;
	const char	*command_string;
	const char	*short_usage_text;
	const char	*one_line_help_text;
}
command_help[] =
	{
		{COMMAND_LOAD, "load", "load files",
			"load bytecode files or shared objects"},
		{COMMAND_EXIT, "exit", "exit",
			"exit debugger"},
		{COMMAND_CALL, "call", "call predicate",
			"call a predicate (assumes registers are valid)"},
		{COMMAND_MODULES, "modules", "modules",
			"list currently loaded modules"},
		{COMMAND_HELP, "help", "help [command]", 
			"help on commands"},
		{COMMAND_PROC, "proc", "proc entrypoint", 
			"set instruction pointer to a given entrypoint"},
		{COMMAND_RUN, "run", "run predicate", 
			"run a simple i/o predicate such as main/2"},
		{COMMAND_SET, "set", "set variable value", 
			"set a debugger variable"},
		{COMMAND_DISASM, "disasm", "disasm", 
			"disassemble bytecode from modules"},
		{COMMAND_UNLOAD, "unload", "unload files", 
			"unload files"},
		{COMMAND_WHERE, "where", "where", 
			"print stack trace"},
		{COMMAND_PRINT, "print", "print variable", 
			"print value of debugger variable"},
		{COMMAND_STEP, "step", "step", 
			"execute current bytecode instruction"}
	/*
	** XXX: Lots more to finish here.
	*/
	};


static void
toplevel(void);

static void
init_all_modules(void);

static Command
parse_line(char *line);

static void
usage(void);

static void
process_commandline(int argc, char *argv[]);

static void
disasm_modules(MB_SList module_list);

static void
load_files(MB_SList file_list);

static void
unload_files(MB_SList file_list);

static void
load_file(char *filename);

static void
unload_file(char *filename);

static void
not_implemented(const char *command);

static MB_Bool
is_bytecode_file(const char *filename);

static MB_Bool
is_shared_object(const char *filename);

static void
load_bytecode_file(const char *bc_filename);

static void
load_bytecodes(FILE *fp, const char *filename);

static MB_Code_Addr_Module*
new_code_addr_mod(MB_Code *code_addr, const char *mod_name);

static Bytecode_Module_Info*
new_module_info(void);

static void
unload_bytecode_file(const char *filename);

static void
testxxx(MB_SList args);

static int
label_compare(const MB_Short label1, const MB_Short label2);

static void
load_shared_object(const char *filename);

static void
unload_shared_object(char *filename);

static void
load_default_shared_objects(void);

static void
help(MB_SList args);

static void
list_modules(void);

static void
command_run(MB_SList args);

static MB_Bool
read_bytecode(MB_Bytecode *bc_p);

static void
increment_ip(void);

static void
execute_bytecode(MB_Bytecode bc);

static void
command_step(void);

static void
command_set(MB_SList args);

static void
command_print(MB_SList args);

static void
print_regs(void);

static void
command_set(MB_SList args);

static void
command_set_ip_to_entrypoint(MB_SList args);

static int
slist_length(MB_SList list);

static void*
slist_nth(MB_SList list, int n);

/* Implementation */

/*
**	This is called from Mercury source.
*/
int
BC_call_mbi(void)
{
	/*
	** XXX: HACK.
	*/
	return BC_mbi_main(0, NULL);
}

/*
**	As a first cut, we will call this procedure
**	from a Mercury program via pragma_c. This
**	means at this point the following would already 
**	have been done:
**		- the Boehm GC is initialised
**		- the runtime engine is initialised
**		- the Mercury modules in libmercury are initialised
**	Now in order to call C code from here, we dlopen the
**	shared objects and use dlsym to look up entry points.
**	(This means we can call only -exported- predicates
**	since local predicates have no external entry point
**	in shared objects.) Note that even though libmer and
**	libmercury have already been linked by the Mercury
**	program that calls this procedure, we do not have
**	handles on these shared objects, hence we need to
**	do another dlopen to get their handles.
**
**	To handle nondet compiled Mercury code, we will need to
**	create a version of runtime/engine.call_engine() that
**	allows nondet calls. The current call_engine() should
**	be ok for det calls, and for semidet calls we need only
**	check the value of register r1 to see if it succeeded.
**
**	Note: If this procedure is called from Mercury then
**	argc and argv probably won't make much sense, so
**	we can forget about them. We'd then have to load in
**	all shared objects and bytecode files from the
**	toplevel of the bytecode interpreter.
*/
int
BC_mbi_main(int argc, char* argv[])
{
	init_all_modules();

	/*
	** XXX: don't do this since we call from mdb.m
	** Of course, we should pass commandline from mdb.m to here!
	**
	** process_commandline(argc, argv);
	*/

	load_default_shared_objects();

	toplevel();

	return EXIT_SUCCESS;
} /* end main() */

static void
toplevel(void)
{
	char		*line;
	static char	prompt[] = "mdb> ";
	Command		command;

	while ((line = readline(prompt)) != NULL)
	{
		command = parse_line(line);

		/*
		** Don't add to history if line is blank.
		*/
		if (command.name != COMMAND_NONE) {
			add_history(line);
		}

		switch (command.name)
		{
		case COMMAND_DISASM:
			disasm_modules(command.args);
			break;
		case COMMAND_ERROR:
			MB_util_error("command is not known. Try \"help\".");
			break;
		case COMMAND_EXIT:
			return; /* XXX: not neat. C has no multilevel break */
			break;
		case COMMAND_HELP:
			help(command.args);
			break;
		case COMMAND_LOAD:
			load_files(command.args);
			break;
		case COMMAND_MODULES:
			list_modules();
			break;
		case COMMAND_NONE:
			/* do nothing */
			break;
		case COMMAND_PRINT:
			command_print(command.args);
			break;
		case COMMAND_PROC:
			command_set_ip_to_entrypoint(command.args);
			break;
		case COMMAND_RUN:
			command_run(command.args);
			break;
		case COMMAND_SET:
			command_set(command.args);
			break;
		case COMMAND_STEP:
			command_step();
			break;
		case COMMAND_TESTXXX:
			testxxx(command.args);
			break;
		case COMMAND_UNLOAD:
			unload_files(command.args);
			break;
		default:
			not_implemented("unknown");
			break;
		}
	} /* end while */

	return;
} /* end toplevel */

/*
** Set a variable used by the debugger.
** xxx: there should be a table of variables and values
** rather than hacking specific cases.
*/
static void
command_set(MB_SList args)
{
	/*
	** xxx: stub
	*/
	return;
}

static void
command_set_ip_to_entrypoint(MB_SList args)
{
	char			*entrypoint;
	MB_Code_Addr_Module	*code_addr_module_p;

	assert(slist_length(args) == 1);

	entrypoint = MB_slist_head(args);

XXXdebug(In command_set_ip_to_entrypoint, s, entrypoint);
	if ( ! MB_dict_lookup(entrypoint, MB_bytecode_proc_dict,
		(void**) &code_addr_module_p))
	{
		/* 
		** the entrypoint should be in the dictionary of
		** bytecode procedure entrypoints.
		*/
		assert(FALSE);
	} else {
		MB_bmachine.ip = code_addr_module_p->code_addr;
XXXdebug(In command_set_ip_to_entrypoint, p, MB_bmachine.ip);
XXXdebug(In command_set_ip_to_entrypoint, s, code_addr_module_p->mod_name);
		/* xxx do anything with module name? */
	}
}

static int
slist_length(MB_SList list)
{
	int	len;

	for (len=0; ! MB_slist_null(list); len++, list=MB_slist_tail(list))
		/* empty */ ;
	return len;
}

static void*
slist_nth(MB_SList list, int n)
{
	int	cur = 0;

	/* xxx: head and tail will fail if out of bounds */
	while (TRUE) {
		if (cur == n) {
			return MB_slist_head(list);
		} else {
			cur++;
			list=MB_slist_tail(list);
		}
	}
}

static void
command_print(MB_SList args)
{
	char	*arg;

	while ( ! MB_slist_null(args))
	{
		arg = MB_slist_head(args);

		if (MB_streq(arg,"ip")) {
			MB_util_print("%s = 0x%p", arg, MB_bmachine.ip);
		} else if (MB_streq(arg,"regs")) {
			print_regs();
		} else {
			MB_util_print("Variable \"%s\" not known", arg);
		}

		args = MB_slist_tail(args);
	} /* end while */

} /* end command_print() */

/*
** Print the registers of the Mercury runtime.
*/
static void
print_regs(void)
{
	/* xxx hack hack -- how many virtual regs are there? */
	const int 	max_regs = 20;
	int		i;
	int		width = 2 * sizeof(Code *); /* 2 hex digits per byte */

	MB_util_print("succip = 0x%.*p", width, succip);
	MB_util_print("hp     = 0x%.*p", width, hp);
	MB_util_print("sp     = 0x%.*p", width, sp);
	MB_util_print("curfr  = 0x%.*p", width, curfr);
	MB_util_print("maxfr  = 0x%.*p", width, maxfr);

	/*
	** xxx: this code is -way- fugly. do this more neatly.
	*/
	MB_util_print("r01=0x%.*p  r02=0x%.*p  r03=0x%.*p",
		width, r1, width, r2, width, r3);
	MB_util_print("r04=0x%.*p  r05=0x%.*p  r06=0x%.*p",
		width, r4, width, r5, width, r6);
	MB_util_print("r07=0x%.*p  r08=0x%.*p  r09=0x%.*p",
		width, r7, width, r8, width, r9);
	MB_util_print("r10=0x%.*p  r11=0x%.*p  r12=0x%.*p",
		width, r10, width, r11, width, r12);
	MB_util_print("r13=0x%.*p  r14=0x%.*p  r15=0x%.*p",
		width, r13, width, r14, width, r15);
	MB_util_print("r16=0x%.*p  r17=0x%.*p  r18=0x%.*p",
		width, r16, width, r17, width, r18);
	MB_util_print("r19=0x%.*p  r20=0x%.*p  r21=0x%.*p",
		width, r19, width, r20, width, r21);
	MB_util_print("r22=0x%.*p  r23=0x%.*p  r24=0x%.*p",
		width, r22, width, r23, width, r24);
	MB_util_print("r25=0x%.*p  r26=0x%.*p  r27=0x%.*p",
		width, r25, width, r26, width, r27);
	MB_util_print("r28=0x%.*p  r29=0x%.*p  r30=0x%.*p",
		width, r28, width, r29, width, r30);
	MB_util_print("r31=0x%.*p  r32=0x%.*p",
		width, r31, width, r32);

#if 0
	for (i=0; i <= max_regs; i++) {
		MB_util_print("register[%d] = 0x%p", i, virtual_reg(i));
	}
#endif /* 0 */

}

static void
command_run(MB_SList args)
{
	/* XXX: stub 
	**
	** For compiled Mercury code need to call runtime.engine.call_engine
	** (or possibly a modified version that deals with nondet calls).
	** Pass in the entry point returned from a call to dlsym(3)
	** with the mangled proc name as an argument.
	**
	** For bytecode, push the current module and bytecode instruction 
	** pointer, 
	*/
	not_implemented("command_run()");
	return;
}

/*
** XXX: This is way primitive currently. We just show usage of all commands
** rather than give help on requested commands.
** This does not yet have high priority.
**
** XXX:This sort of thing is probably better implemented in Mercury
** and called from the C code of the debugger. In fact, as much as possible
** should be done in Mercury.
*/
static void
help(MB_SList args)
{
	int	i;
	const char
		*fmt = "%-20s -- %s";
		

	for (i=0; i < sizeof(command_help) / sizeof(*command_help); i++)
	{
		MB_util_print(fmt, command_help[i].short_usage_text,
			command_help[i].one_line_help_text);
	}
	return;
}

static void
testxxx(MB_SList args)
{
	char	*arg;

	while ( ! MB_slist_null(args))
	{
		arg = MB_slist_head(args);

		if (strcmp(arg,"0") == 0)
		{
			MB_print_shared_object_dict();
		}
		else if (strcmp(arg, "1") == 0)
		{
			MB_util_print("Test no longer exists");
			/* print_bmachine(); */
		}
		else if (strcmp(arg, "2") == 0)
		{
			MB_print_bytecode_module_dict();
		}
		else if (strcmp(arg, "3") == 0)
		{
			MB_print_bytecode_proc_dict();
		}
		else
		{
			MB_util_print("Test \"%s\" not known", arg);
		}

		args = MB_slist_tail(args);
	}
}

static void
disasm_modules(MB_SList module_list)
{
	Bytecode_Module_Info	*mod_info_p;

	for ( ;
		! MB_slist_null(module_list) ;
		module_list = MB_slist_tail(module_list))
	{
		if ( ! MB_dict_lookup(
			MB_slist_head(module_list), MB_bytecode_module_dict,
			(void*) &mod_info_p))
		{
			MB_util_error("Module \"%s\" not loaded",
				MB_slist_head(module_list));
		} else {
			int	i;

			for (i=0; i < mod_info_p->top; i++) {
				printf("%06d: ", i);
				MB_print_bytecode(mod_info_p->code[i]);
			}
		} /* else */
	} /* for */

	return;
} /* disasm_modules */

static void
list_modules()
{
	MB_CString	mod_name, next_mod_name;
	int		i;
	MB_Dict		dicts[] = {
				MB_shared_object_dict, 
				MB_bytecode_module_dict};

	for (	i=0;
		i < sizeof(dicts) / sizeof(*dicts); 
		i++)
	{
		if (MB_dict_first_key(dicts[i], (void**) &mod_name))
		{
			printf("%s\n", mod_name);
			while ( MB_dict_next_key(dicts[i], (void*) mod_name,
				(void**) &next_mod_name))
			{
				printf("%s\n", next_mod_name);
				mod_name = next_mod_name;
			}
		}
	}
} /* list_modules */


static void
init_all_modules()
{
	MB_machine_init();
	return;
}

static void
load_files(MB_SList file_list)
{
	while ( ! MB_slist_null(file_list)) {
		load_file(MB_slist_head(file_list));
		file_list = MB_slist_tail(file_list);
	}

	return;
}


static void
unload_files(MB_SList file_list)
{
	while ( ! MB_slist_null(file_list)) {
		unload_file(MB_slist_head(file_list));
		file_list = MB_slist_tail(file_list);
	}

	return;
}

static void
not_implemented(const char *command)
{
	MB_util_error("\"%s\" is not yet implemented.", command);
	return;
}

static Command
parse_line(char *line)
{
	Command 		ret_command;
	static const char	white_space_s[] = " \t";
	char			*tok;
	char			*tmp_line;

	tmp_line = MB_strdup(line);
	ret_command.args = MB_slist_nil();

	tok = strtok(tmp_line, white_space_s);
	if (NULL == tok) {
		ret_command.name = COMMAND_NONE;
	} else {
		/*
		** XXX: Note that "?" and "quit" are not documented.
		*/
		if (strcmp(tok, "call") == 0) {
			ret_command.name = COMMAND_CALL;
		} else if (strcmp(tok, "disasm") == 0) {
			ret_command.name = COMMAND_DISASM;
		} else if (strcmp(tok, "exit") == 0) {
			ret_command.name = COMMAND_EXIT;
		} else if (strcmp(tok, "help") == 0) {
			ret_command.name = COMMAND_HELP;
		} else if (strcmp(tok, "load") == 0) {
			ret_command.name = COMMAND_LOAD;
		} else if (strcmp(tok, "modules") == 0) {
			ret_command.name = COMMAND_MODULES;
		} else if (strcmp(tok, "print") == 0) {
			ret_command.name = COMMAND_PRINT;
		} else if (strcmp(tok, "proc") == 0) {
			ret_command.name = COMMAND_PROC;
		} else if (strcmp(tok, "quit") == 0) {
			ret_command.name = COMMAND_EXIT;
		} else if (strcmp(tok, "run") == 0) {
			ret_command.name = COMMAND_RUN;
		} else if (strcmp(tok, "step") == 0) {
			ret_command.name = COMMAND_STEP;
		} else if (strcmp(tok, "test") == 0) {
			ret_command.name = COMMAND_TESTXXX;
		} else if (strcmp(tok, "unload") == 0) {
			ret_command.name = COMMAND_UNLOAD;
		} else if (strcmp(tok, "?") == 0) {
			ret_command.name = COMMAND_HELP;
		} else {
			ret_command.name = COMMAND_ERROR;
		}

		while ((tok = strtok(NULL, white_space_s)) != NULL) {
			ret_command.args = 
				MB_slist_cons(MB_strdup(tok), ret_command.args);
		}
	}

	/*
	** XXX: Use Boehm GC
	** free(tmp_line);
	*/
	return ret_command;
}


static void
usage(void)
{
	fprintf(stderr, "Usage: %s [-h] files\n", program_name);
}

static void
process_commandline(int argc, char *argv[])
{
	int	c;

	/* We do this in case we change the program name. */
	program_name = argv[0];

	/* Don't use default error messages from getopt() */
	opterr = 0;

	/* Read options */
	while ((c = getopt(argc,argv,"h")) != EOF) {
		switch (c) {
			case 'h':
				usage();
				exit(EXIT_SUCCESS);
				break;
			default:
				usage();
				exit(EXIT_FAILURE);
				break;
		}
	}

	/* 
	** We _must_ have a file argument.
	** Load all file arguments.
	** XXX: This shouldn't necessarily be true. We should
	** be able to load all modules from the mbi toplevel.
	*/
	if (optind == argc) {
		usage();
	} else {
		/* 
		** Process each bytecode file or shared object in order.
		*/
		int 	i;

		for (i = optind; i < argc; i++) {
			load_file(argv[i]);
		}
	} /* end else */
	
	return;
}

/*
** Load either a bytecode file or a shared object.
*/
static void
load_file(char *filename)
{
	if (is_bytecode_file(filename)) {
		load_bytecode_file(filename);
	} else if (is_shared_object(filename)) {
		load_shared_object(filename);
	} else {
		MB_util_error("file extension is not known.");
	}

	return;
}

/*
** Unload either a bytecode file or a shared object.
*/
static void
unload_file(char *filename)
{
	if (is_bytecode_file(filename)) {
		unload_bytecode_file(filename);
	} else if (is_shared_object(filename)) {
		unload_shared_object(filename);
	} else {
		MB_util_error("file extension is not known.");
	}

	return;
}

static MB_Bool
is_bytecode_file(const char *filename)
{
	return MB_has_extension(filename, bytecode_file_extension);
}


static MB_Bool
is_shared_object(const char *filename)
{
	return MB_has_extension(filename, shared_obj_extension);
}

/*
** XXX: We really should use an API similar to dlopen/dlsym/dlclose
** for accessing bytecode files. Possibly use an environment variable
** MERCURY_BC_PATH in analogy with LD_LIBRARY_PATH.
** This is not yet priority.
*/
static void
load_bytecode_file(const char *filename)
{
	FILE	*fp;

	if ((fp = fopen(filename, "r")) == NULL) {
		MB_util_error("cannot open bytecode file \"%s\".", filename);
	} else {
		MB_Short	version_number;
		MB_Short	expected_version = 0x9;
		

		if ( ! MB_read_bytecode_version_number(fp, &version_number)) {
			MB_util_error("cannot read bytecode version number "
				"in bytecode file \"%s\"", filename);
			return;
		}

		if (expected_version != version_number) {
			MB_util_error("incorrect bytecode version number in "
				"bytecode file \"%s\"", filename);
			return;
		}

		MB_util_print("Loading bytecode file \"%s\"", filename);
		load_bytecodes(fp, filename);
		fclose(fp);
	}
	return;
} /* end load_bytecode_file */

/*
** Load the bytecodes from file pointer `fp', where the filename
** of the module is `filename'.
**
** XXX: We simply store the bytecodes sequentially in the code area.
** This makes UNloading of bytecode files difficult.
** One way to unload is simply to put NOOPs in the area containing the
** unloaded module. Another alternative is to reload all the modules
** so that we remove holes from the code area. Yet another alternative
** is to use a different data structure for the code area.
*/
static void
load_bytecodes(FILE *fp, const char *filename)
{
	MB_Bytecode		bytecode;
	Bytecode_Module_Info	*mod_info_p;
	MB_Code			*current_bc_addr;

	mod_info_p = new_module_info();
	/* XXX: Module name needn't be filename */
	mod_info_p->mod_name = MB_strdup(filename);
	/* XXX: should check if this module has already been loaded. */
	MB_dict_insert(MB_strdup(filename), (void*)mod_info_p, 
		&MB_bytecode_module_dict);

	for (	current_bc_addr = (MB_Code*) &(mod_info_p->code) ;
		MB_read_bytecode(fp, &bytecode) ;
		mod_info_p->top++, current_bc_addr += sizeof(bytecode))
	{
		mod_info_p->code[mod_info_p->top] = bytecode;
		assert(mod_info_p->top < MB_MAX_CODE); /* XXX */

		switch (bytecode.id)
		{
		case MB_BC_enter_proc:
			/*
			** Store proc address in MB_bytecode_proc_dict.
			*/ 
			{
			MB_CString		proc_name;
			MB_Code_Addr_Module	*code_addr_mod_p;
	
			/* 
			** XXXX: Should we store an index into code[] or
			** a machine address instead?
			*/
			code_addr_mod_p = new_code_addr_mod(
				current_bc_addr, 
				filename);
					
			proc_name = MB_strdup(bytecode.opt.enter_proc.
				proc_id.string);
			MB_dict_insert(proc_name,
				code_addr_mod_p,
				&MB_bytecode_proc_dict);
			}
			break;
		case MB_BC_label:
			/* store code address of label */
			MB_dict_insert((void*)bytecode.opt.label.label,
				(void*) mod_info_p->top,
				&(mod_info_p->label_dict));
			break;
		case MB_BC_enter_pred:
			/* XXX: Should store pred info in mod_info_p */
			break;
		default:
			/* For other bytecodes, needn't do anything. */
			break;
		}
	} /* end for */

	return;
} /* end load_bytecodes */

static MB_Code_Addr_Module*
new_code_addr_mod(MB_Code *code_addr, const char *mod_name)
{
	MB_Code_Addr_Module	*code_mod_p;

	code_mod_p = MB_malloc(sizeof(MB_Code_Addr_Module));
	code_mod_p->code_addr = code_addr;
	code_mod_p->mod_name = MB_strdup(mod_name);

	return code_mod_p;
}

static void
unload_bytecode_file(const char *filename)
{
	/*
	** XXX: Not yet implemented.
	** Method:
	**	- Remove entry from dictionary of bytecode modules
	*	- Remove code from code area
	**	- Should also check for dangling references?
	*/
	not_implemented("unload_bytecode_file");
	return;
} /* end load_bytecode_file */

static Bytecode_Module_Info*
new_module_info()
{
	Bytecode_Module_Info	*bc_mod_info_p;

	bc_mod_info_p = MB_malloc(sizeof(Bytecode_Module_Info));
	bc_mod_info_p->mod_name = NULL;
	bc_mod_info_p->label_dict = 
		MB_dict_new((MB_KeyComparison)label_compare);

	bc_mod_info_p->top = 0;
	memset(bc_mod_info_p->code, 0x0, sizeof(bc_mod_info_p->code));

	/* XXX: Add pred info later. */
	#if 0
	bc_mod_info_p->pred_dict = MB_dict_new((MB_KeyComparison)strcmp);
	#endif /* 0 */

	return bc_mod_info_p;
} /* new_module_info */


static int
label_compare(const MB_Short label1, const MB_Short label2)
{
	if (label1 == label2) {
		return 0;
	} else if (label1 < label2) {
		return (-1);
	} else
		return 1;
}

/*
** Load a shared object into the dictionary of shared objects.
*/
static void
load_shared_object(const char *filename)
{
	void	*handle;

	/*
	** XXX: Need to review shared library mechanisms across
	** supported platforms (and others!). The dlopen family
	** are pervasive across Unixes. Need to check Windows{95,NT}.
	** Presumably, we don't care about MacOS. 
	** Other platforms are marginal.
	*/
	if ((handle = dlopen(filename, RTLD_LAZY)) == NULL) {
		MB_util_error("cannot open shared object \"%s\".",
			filename);
	} else {
		/*
		** XXX: We need to stored the handle in a table so we
		** can look symbols up at runtime.
		*/
		MB_util_print("Loading shared object \"%s\"", filename);
		/* XXX: check if this module has already been loaded */
		MB_dict_insert(filename, handle, &MB_shared_object_dict);
	}
	return;
}

/*
** Unload a shared object from the dictionary of shared objects.
*/
static void
unload_shared_object(char *filename)
{
	void	*handle;

	if (MB_dict_lookup(filename, MB_shared_object_dict, &handle))
	{
		MB_dict_delete(filename, &MB_shared_object_dict);
		dlclose(handle);
	}
	else
	{
		MB_util_error("cannot unload shared object \"%s\".",
			filename);
	}

	return;
}


static void
load_default_shared_objects(void)
{
	const char	**lib_p;
	static const char*	
	default_shared_objects[] = {"libmer.so", "libmercury.so", NULL};

	lib_p = default_shared_objects;
	assert(lib_p != NULL);

	while (*lib_p != NULL) {
		load_shared_object(*lib_p);
		lib_p++;
	}
	return;
}


/*
** Execute the current bytecode at the bytecode IP.
*/
static void
command_step(void)
{
	MB_Bytecode	bc;

	if (read_bytecode(&bc)) {
		execute_bytecode(bc);
	} else {
		MB_util_error("No bytecode at instruction pointer");
	}
}

static void
execute_bytecode(MB_Bytecode bc)
{
	/* 
	** XXX: this is currently a stub.
	**
	** Obviously if the command is a call or jump etc, we
	** have to adjust the IP appropriately. Right now we just
	** hack it to test.
	*/

	MB_print_bytecode(bc); /* xxx debug */

	switch (bc.id)
	{
	case MB_BC_enter_pred:
		/*
		** xxx: check set of breakpoints and stop if
		** a breakpoint is set on this pred.
		*/
		break;
	case MB_BC_enter_proc:
		/*
		** xxx: check set of breakpoints and stop if
		** a breakpoint is set on this proc.
		*/
		break;
	case MB_BC_pickup_arg:
		/*
		** XXX: WRONG WRONG
		** This is not how we dereference the variable slots
		** on the stack. Since a) there's other stuff on the
		** det stack and b) we may have the variable slots
		** on the nondet stack instead.
		*/
		detstackvar(bc.opt.pickup_arg.to_var) = 
			virtual_reg(bc.opt.pickup_arg.from_reg);
		break;
	case MB_BC_label:
		/*
		** XXX: Need we do anything at all with labels?
		*/
		break;
	case MB_BC_context:
		/*
		** XXX: we should update current module and source line.
		** should put these in a stack?
		*/
		break;
	case MB_BC_assign:
		detstackvar(bc.opt.assign.to_var) = 
			detstackvar(bc.opt.assign.from_var);
		break;
	case MB_BC_place_arg:
		/*
		** XXX: WRONG WRONG
		** See note for pickup_arg above.
		*/
		virtual_reg(bc.opt.place_arg.to_reg) = 
			detstackvar(bc.opt.place_arg.from_var);
		break;
	case MB_BC_endof_proc:
		/*
		** xxx: possibly jump to end of proc and stop.
		*/
		break;
	case MB_BC_endof_pred:
		/*
		** xxx: possibly jump to end of pred and stop.
		*/
		break;
	default:
		/*
		** XXX: warn that instruction is not yet implemented.
		*/
		break;
	}

	/*
	** XXX: fix IP updating.
	*/
	if (TRUE) {
		increment_ip();
	}

	return;
}

/*
**	Increment instruction pointer of the bytecode machine.
*/
static void
increment_ip(void)
{
	MB_bmachine.ip += sizeof(MB_Bytecode);
	return;
}

/*
**	Return the bytecode at the instruction pointer.
**	Do not increment the IP here, however.
*/
static MB_Bool
read_bytecode(MB_Bytecode *bc_p)
{
	/*
	** XXX: also check that we don't fall off the end of code[] ?
	*/
	if (MB_bmachine.ip != NULL) {
		memcpy(bc_p, MB_bmachine.ip, sizeof(MB_Bytecode));
		return TRUE;
	} else {
		return FALSE;
	}
} /* end read_bytecode() */

#ifdef	TEST_MBI

int
main(void)
{
	/*
	** XXX: Add some unit tests here.
	*/

	return EXIT_SUCCESS;
}

#endif /* TEST_MBI */
