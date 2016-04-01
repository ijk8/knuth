% Change file for the WEAVE processor, for use on Berkeley UNIX systems.
%   This file was created by Howard Trickey and Pavel Curtis.

% History:
%  11/29/82 HWT Original version. This modifies weave to allow a new
%               control sequence:
%                       @=...text...@>   Put ...text... verbatim on a line
%                                        by itself in the Pascal output.
%                                        (argument must fit on one line)
%               This control sequence facilitates putting #include "gcons.h"
%               (for example) in files meant for the pc compiler.
%               Also, there is a command line option, -c, which means that
%               only the modules affected by the change file are to generate
%               TeX output.  (All the limbo stuff still goes to the output
%               file, as does the index and table of contents.)
%
%  2/12/83 HWT  Brought up for use with version 1.3.  Uses Knuth's new
%               control sequences for verbatim Pascal (as above, without
%               the "on one line" part), and the force_line (@\) primitive.
%               Also, he added stuff to keep track of changed modules, and
%               output enough information that macros can choose only to
%               print changed modules.  This isn't as efficient as my
%               implementation because I avoided outputting the text for
%               non-changed modules altogether, but this feature won't be
%               used too often (just for TeX and TeXware), so Knuth's
%               solution is accepted.
%               The change file changes that used
%               to implement these features have been removed.
%               There is a -x flag to cause WEAVE to omit cross referencing
%               of identifiers, and index and T.of.C. processing.
%               This, too, is unnecessary, for one could simply redefine some
%               WEB macros to avoid the printing, but there are only a couple
%               of easy changes, so they have been made.
%
%  2/18     HWT Increased stack size to 400 (not for TeX-related programs).
%
%  3/18     HWT Brought up for Version 1.5.  Made it print newline at end of
%               run.
%
%  4/13     PC  Merged with Pavel's version, including adding a call to
%               exit() at the end of the program, based upon the value of
%               `history'.
%  4/16     PC  Brought up to version 1.5 released with TeX 0.97 in April 1983
%  6/29     HWT Brought up to version 1.7 released with TeX 0.99 in June 1983,
%		introducing a new change file format
%  7/17	    HWT Brought up to version 2.0 released with TeX 0.999 in July 1983
%  7/29     HWT Brought up to version 2.1
% 11/17     HWT Brought up to version 2.4 released with TeX 1.0.  Made
%		changes to use C routines for I/O, for speedup.
%  1/31     HWT Brought up to version 2.6
% 12/28/85  PAM Brought up to version 2.8 (like 2.7, version number only)
% 3/6/87    PAM Brought up to version 2.9 (like 2.8, version number only)
% 8/10/89   don Brought up to version 3.1, with `otherwise' fixed too
% 8/31/89   don Brought up to version 4, with all possible characters enabled
% 10/16/89  don fixed bug when ".web" and ".ch" are explicitly stated
% 3/25/90   don changed version number to 4.1
% 9/6/90    don changed version number to 4.2
% 9/19/91   don changed version number to 4.3
% 1/12/92   don changed version number to 4.4

% NOTE: The module numbers refer to the standard WEB manual (CS 980).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [0] WEAVE: print changes only
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
\pageno=\contentspagenumber \advance\pageno by 1
@y
\pageno=\contentspagenumber \advance\pageno by 1
\let\maybe=\iffalse
\def\title{WEAVE changes for Berkeley {\mc UNIX}}
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [1] Change banner message
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@d banner=='This is WEAVE, Version 4.4'
@y
@d banner=='This is WEAVE, Version 4.4 for SunOS'
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [2] add input and output, remove other files, add ref to scan_args,
% [2]       and #include external definition for exit(), etc.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
program WEAVE(@!web_file,@!change_file,@!tex_file);
label end_of_WEAVE; {go here to finish}
const @<Constants in the outer block@>@/
type @<Types in the outer block@>@/
var @<Globals in the outer block@>@/
@<Error handling procedures@>@/
@y
program WEAVE(@!input,@!output);
label end_of_WEAVE; {go here to finish}
const @<Constants in the outer block@>@/
type @<Types in the outer block@>@/
var @<Globals in the outer block@>@/
@\
@=#include "tangext.h"@>
@\@/
@<Error handling procedures@>@/
@<|scan_args| procedure@>@/
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [3] Show statistics
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@d stat==@{ {change this to `$\\{stat}\equiv\null$'
  when gathering usage statistics}
@d tats==@t@>@} {change this to `$\\{tats}\equiv\null$'
  when gathering usage statistics}
@y
@d stat== {I'm gathering usage statistics}
@d tats== {because I have to know how close \TeX\ comes to the limits}
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [4] compiler options
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@{@&$C-,A+,D-@} {no range check, catch arithmetic overflow, no debug overhead}
@!debug @{@&$C+,D+@}@+ gubed {but turn everything on when debugging}
@y
@=(*$C-*)@> {no range check}
@!debug @=(*$C+*)@>@+ gubed {but turn everything on when debugging}
@\
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [7] Fix others:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@d othercases == others: {default for cases not listed explicitly}
@y
@d othercases == otherwise {SunOS Pascal default cases}
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [8] Constants: Make stack_size=400 instead of 200
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@!stack_size=200; {number of simultaneous output levels}
@y
@!stack_size=400; {number of simultaneous output levels}
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [17] enable maximum character set
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
for i:=1 to @'37 do xchr[i]:=' ';
for i:=@'200 to @'377 do xchr[i]:=' ';
@y
for i:=1 to @'37 do xchr[i]:=chr(i);
for i:=@'200 to @'377 do xchr[i]:=chr(i);
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [20] terminal output: use standard i/o
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@d print(#)==write(term_out,#) {`|print|' means write on the terminal}
@y
@d term_out==output
@d print(#)==write(term_out,#) {`|print|' means write on the terminal}
@z

@x
@<Globals...@>=
@!term_out:text_file; {the terminal as an output file}
@y

@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [21] init terminal
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@ Different systems have different ways of specifying that the output on a
certain file will appear on the user's terminal. Here is one way to do this
on the \PASCAL\ system that was used in \.{TANGLE}'s initial development:
@^system dependencies@>

@<Set init...@>=
rewrite(term_out,'TTY:'); {send |term_out| output to the terminal}
@y
@ Different systems have different ways of specifying that the output on a
certain file will appear on the user's terminal.
@^system dependencies@>

@<Set init...@>=
; {nothing need be done}
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [22] flush terminal buffer
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@d update_terminal == break(term_out) {empty the terminal output buffer}
@y
@d update_terminal == flush(term_out) {empty the terminal output buffer}
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [24] open input files
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@ The following code opens the input files.  Since these files were listed
in the program header, we assume that the \PASCAL\ runtime system has
already checked that suitable file names have been given; therefore no
additional error checking needs to be done. We will see below that
\.{WEAVE} reads through the entire input twice.
@^system dependencies@>

@p procedure open_input; {prepare to read |web_file| and |change_file|}
begin reset(web_file); reset(change_file);
end;
@y
@ The following code opens the input files.
This is called after |scan_args| has filled the file name variables
appropriately.
@^system dependencies@>

@p procedure open_input; {prepare to read |web_file| and |change_file|}
begin reset(web_file,web_name);
      reset(change_file,change_name);
end;
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [26] opening tex file
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@ The following code opens |tex_file|.
Since this file was listed in the program header, we assume that the
\PASCAL\ runtime system has checked that a suitable external file name has
been given.
@^system dependencies@>

@<Set init...@>=
rewrite(tex_file);
@y
@ The following code opens |tex_file|.
The |scan_args| procedure is used to set up |tex_name| as required.
@^system dependencies@>

@<Set init...@>=
scan_args;
rewrite(tex_file,tex_name);
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [28] faster input_ln
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@p function input_ln(var f:text_file):boolean;
  {inputs a line or returns |false|}
var final_limit:0..buf_size; {|limit| without trailing blanks}
begin limit:=0; final_limit:=0;
if eof(f) then input_ln:=false
else  begin while not eoln(f) do
    begin buffer[limit]:=xord[f^]; get(f);
    incr(limit);
    if buffer[limit-1]<>" " then final_limit:=limit;
    if limit=buf_size then
      begin while not eoln(f) do get(f);
      decr(limit); {keep |buffer[buf_size]| empty}
      if final_limit>limit then final_limit:=limit;
      print_nl('! Input line too long'); loc:=0; error;
@.Input line too long@>
      end;
    end;
  read_ln(f); limit:=final_limit; input_ln:=true;
  end;
end;
@y
With Berkeley {\mc UNIX} we call an external C procedure, |line_read|.
That routine fills |buffer| from 0 onwards with the |xord|'ed values
of the next line, setting |limit| appropriately (ignoring trailing
blanks).
It will stop if |limit=buf_size|, and the following will cause an error
message.
Note: for bootstrapping purposes it is all right to use the original form
of |input_ln|; it will just run slower.

@p function input_ln(var f:text_file):boolean;
  {inputs a line or returns |false|}
begin limit:=0;
if test_eof(f) then input_ln:=false
else  begin line_read(f);
    if limit=buf_size then
      begin
      decr(limit); {keep |buffer[buf_size]| empty}
      print_nl('! Input line too long'); loc:=0; error;
@.Input line too long@>
      end;
   input_ln:=true;
  end;
end;
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [50] don't enter xrefs if no_xref set
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@d append_xref(#)==if xref_ptr=max_refs then overflow('cross reference')
  else  begin incr(xref_ptr); num(xref_ptr):=#;
    end

@p procedure new_xref(@!p:name_pointer);
label exit;
var q:xref_number; {pointer to previous cross reference}
@!m,@!n: sixteen_bits; {new and previous cross-reference value}
begin if (reserved(p)or(byte_start[p]+1=byte_start[p+ww]))and
@y
If the user has sent the |no_xref| flag (the -x option of the command line),
then it is unnecessary to keep track of cross references for identifers.
If one were careful, one could probably make more changes around module
100 to avoid a lot of identifier looking up.

@d append_xref(#)==if xref_ptr=max_refs then overflow('cross reference')
  else  begin incr(xref_ptr); num(xref_ptr):=#;
    end

@p procedure new_xref(@!p:name_pointer);
label exit;
var q:xref_number; {pointer to previous cross-reference}
@!m,@!n: sixteen_bits; {new and previous cross-reference value}
begin if no_xref then return;
if (reserved(p)or(byte_start[p]+1=byte_start[p+ww]))and
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [122] faster flush_buffer
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
done: for k:=1 to j do write(tex_file,xchr[out_buf[k]]);
@y
done: linewrite(tex_file,j);
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [239] omit index and module names if no_xref set
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@<Phase III: Output the cross-reference index@>=
@y
If the user has set the |no_xref| flag (the -x option on the command line),
just finish off the page, omitting the index, module name list, and table of
contents.

@<Phase III: Output the cross-reference index@>=
if no_xref then begin
        finish_line;
        out("\"); out5("v")("f")("i")("l")("l");
        out4("\")("e")("n")("d");
        finish_line;
        end
else begin
@z

@x
print('Done.');
@y
end;
print('Done.');
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [258] term_in == input, when debugging
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
any error stop will set |debug_cycle| to zero.
@y
any error stop will set |debug_cycle| to zero.

@d term_in==input
@z

@x
@!term_in:text_file; {the user's terminal as an input file}
@y

@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [259] Take out reset(term_in)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
reset(term_in,'TTY:','/I'); {open |term_in| as the terminal, don't do a |get|}
@y

@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [261] print newline at end of run and exit based upon value of history
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@p procedure Phase_I;
@y
@d UNIXexit==e@&x@&i@&t

@p procedure Phase_I;
@z

@x
end.
@y
new_line;
if (history <> spotless) and (history <> harmless_message) then
    UNIXexit(1)
else
    UNIXexit(0);
end.
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [264] system dependent changes--the scan_args procedure
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@* System-dependent changes.
This module should be replaced, if necessary, by changes to the program
that are necessary to make \.{WEAVE} work at a particular installation.
It is usually best to design your change file so that all changes to
previous modules preserve the module numbering; then everybody's version
will be consistent with the printed program. More extensive changes,
which introduce new modules, can be inserted here; then only the index
itself will get a new module number.
@^system dependencies@>
@y
@* System-dependent changes.
The user calls \.{WEAVE} with arguments on the command line.
These are either file names or flags (beginning with '-').
The following globals are for communicating the user's desires to the rest
of the program. The various |file_name| variables contain strings with
the full names of those files, as UNIX knows them.

The only flag that affects weave is |'-x'| whose status is kept in |no_xref|.

@d max_file_name_length==60

@<Globals...@>=
@!web_name,@!change_name,@!tex_name:
        array[1..max_file_name_length] of char;
@!no_xref:boolean;

@ The |scan_args| procedure looks at the command line arguments and sets
the |file_name| variables accordingly.
At least one file name must be present: the \.{WEB} file.  It may have
an extension, or it may omit it to get |'.web'| added.
The \TeX\ output file name is formed by replacing the \.{WEB} file
name extension by |'.tex'|.

If there is another file name present among the arguments, it is the
change file, again either with an extension or without one to get |'.ch'|
An omitted change file argument means that |'/dev/null'| should be used,
when no changes are desired.

An argument beginning with a minus sign is a flag.
Any letters following the minus sign may cause global flag variables to be
set.
Currently, an |x| means that the cross referencing information---the index,
the module name list, and the table of contents---is to be suppressed.

@<|scan_args|...@>=
procedure scan_args;
var dot_pos,i,a: integer; {indices}
@!fname: array[1..max_file_name_length-5] of char; {temporary argument holder}
@!found_web,@!found_change: boolean; {|true| when those file names have
                                        been seen}
begin
found_web:=false;
found_change:=false;
no_xref:=false;
for a:=1 to argc-1 do begin
        argv(a,fname); {put argument number |a| into |fname|}
        if fname[1]<>'-' then begin
                if not found_web then
                        @<Get |web_name|, |pascal_name|, and
                                | pool_name| variables from |fname|@>
                else if not found_change then
                        @<Get |change_name| from |fname|@>
                else  @<Print usage error message and quit@>;
                end
        else @<Handle flag argument in |fname|@>;
        end;
if not found_web then @<Print usage error message and quit@>;
if not found_change then @<Set up null change file@>;
end;

@ Use all of |fname| for the |web_name| if there is a |'.'| in it,
otherwise add |'.web'|.
The other file names come from adding things after the dot.
The |argv| procedure will not put more than |max_file_name_length-5|
characters into |fname|, and this leaves enough room in the |file_name|
variables to add the extensions.

The end of a file name is marked with a |' '|, the convention assumed by 
the |reset| and |rewrite| procedures.

@<Get |web_name|...@>=
begin
dot_pos:=-1;
i:=1;
while (fname[i]<>' ') and (i<=max_file_name_length-5) do begin
        web_name[i]:=fname[i];
        if fname[i]='.' then dot_pos:=i;
        incr(i);
        end;
if dot_pos=-1 then begin
        dot_pos:=i;
        web_name[dot_pos]:='.';
        web_name[dot_pos+1]:='w';
        web_name[dot_pos+2]:='e';
        web_name[dot_pos+3]:='b';
        web_name[dot_pos+4]:=' ';
        end
else web_name[i]:=' ';
for i:=1 to dot_pos do begin
        tex_name[i]:=web_name[i];
        end;
tex_name[dot_pos+1]:='t';
tex_name[dot_pos+2]:='e';
tex_name[dot_pos+3]:='x';
tex_name[dot_pos+4]:=' ';
found_web:=true;
end

@

@<Get |change_name|...@>=
begin
dot_pos:=-1;
i:=1;
while (fname[i]<>' ') and (i<=max_file_name_length-5)
do begin
        change_name[i]:=fname[i];
        if fname[i]='.' then dot_pos:=i;
        incr(i);
        end;
if dot_pos=-1 then begin
        dot_pos:=i;
        change_name[dot_pos]:='.';
        change_name[dot_pos+1]:='c';
        change_name[dot_pos+2]:='h';
        change_name[dot_pos+3]:=' ';
        end
else change_name[i]:=' ';
found_change:=true;
end

@

@<Set up null...@>=
begin
        change_name[1]:='/';
        change_name[2]:='d';
        change_name[3]:='e';
        change_name[4]:='v';
        change_name[5]:='/';
        change_name[6]:='n';
        change_name[7]:='u';
        change_name[8]:='l';
        change_name[9]:='l';
        change_name[10]:=' ';
end

@

@<Handle flag...@>=
begin
i:=2;
while (fname[i]<>' ') and (i<=max_file_name_length-5) do begin
        if fname[i]='x' then no_xref:=true;
        incr(i);
        end;
end

@

@<Print usage error message and quit@>=
begin
print_nl('! Usage: weave webfile[.web] [changefile[.ch]] [-x]');
error;
jump_out;
end

@z
