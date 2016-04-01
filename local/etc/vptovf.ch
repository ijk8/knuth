%   Change file for the VPtoVF processor, for use with GNU Pascal
%   (by Don Knuth; see ../etc-sparc for its prehistory)

% History:
% 2000.04.30 Initial version

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [0] WEAVE: print changes only
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
\pageno=\contentspagenumber \advance\pageno by 1
@y
\pageno=\contentspagenumber \advance\pageno by 1
\let\maybe=\iffalse
\def\title{VP\lowercase{to}VF changes for GNU Pascal}
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [1] Change banner string
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@d banner=='This is VPtoVF, Version 1.5' {printed when the program starts}
@y
@d banner=='This is VPtoVF, Version 1.5 for Linux'
                                         {printed when the program starts}
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [2] Fix filenames in program statement; add `final_end' label; add access
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@p program VPtoVF(@!vpl_file,@!vf_file,@!tfm_file,@!output);
const @<Constants in the outer block@>@/
type @<Types in the outer block@>@/
var @<Globals in the outer block@>@/
@y
@d final_end==9999

@p program VPtoVF(@!output);
label final_end;
const @<Constants in the outer block@>@/
type UNIX_file_name=packed array[1..100] of char;
 @<Types in the outer block@>@/
var @<Globals in the outer block@>@/
@\
@=#include "texwarext.h"@>
@\@/
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [6] Open VPL file
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
reset(vpl_file);
@y
if argc < 4 then begin
    print_ln('Usage: vptovf <vpl-file> <vf-file> <tfm-file>');
    goto final_end;
end;
argv(1, vpl_name);
if testreadaccess(vpl_name) then reset(vpl_file, vpl_name)
else begin print_ln('I can''t read the VPL file!'); goto final_end;
  end;
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [21] Change type of output files and declare extra binary-file variables
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@!vf_file:packed file of 0..255;
@!tfm_file:packed file of 0..255;
@y
@!vf_file,
@!tfm_file            : packed file of ByteCard;
@!vf_name, @!tfm_name,
@!vpl_name             : UNIX_file_name;
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [22] Open output files
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
@ On some systems you may have to do something special to write a
packed file of bytes. For example, the following code didn't work
when it was first tried at Stanford, because packed files have to be
opened with a special switch setting on the \PASCAL\ that was used.
@^system dependencies@>

@<Set init...@>=
rewrite(vf_file); rewrite(tfm_file);
@y
@ On some systems you may have to do something special to write a
packed file of bytes.
@^system dependencies@>

@<Set init...@>=
argv(2, vf_name); argv(3, tfm_name);
rewrite(vf_file, vf_name); rewrite(tfm_file, tfm_name);
@z

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [181] Define label `final_end'; print newline at end of program
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
@x
end.
@y
final_end: print_ln(' '); end.
@z
