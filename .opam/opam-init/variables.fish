set -gx PATH "/home/jose/.opam/system/bin" $PATH;
set -gx OCAML_TOPLEVEL_PATH "/home/jose/.opam/system/lib/toplevel";
set -gx PERL5LIB "/home/jose/.opam/system/lib/perl5:$PERL5LIB";
if [ 0 -eq (count $MANPATH) ]; set -gx MANPATH ""; end;
set -gx MANPATH $MANPATH "/home/jose/.opam/system/man";
set -gx CAML_LD_LIBRARY_PATH "/home/jose/.opam/system/lib/stublibs:/usr/lib/ocaml/stublibs";
