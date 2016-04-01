@x change file for 5chainsi, used to get started: ignores standard input
  @<List the items already known to be at distance |r|@>;
  @<Try all top-down combinations@>;
  @<Try all bottom-up combinations@>;
  @<Input the special cases@>;
@y
  @<Set up the classes at distance 0@>;
  for (r=1;r<=rr;r++) {
    count=0;
    @<List the items already known to be at distance |r|@>;
    @<Try all top-down combinations@>;
    @<Try all bottom-up combinations@>;
  }
@z
@x
@ @<List the items already known to be at distance |r|@>=
@y
@ @<Set up the classes at distance 0@>=
c=lookup(0x0);
setcost(c,0);
c=classify(xx(1));
setcost(c,0);

@ @<List the items already known to be at distance |r|@>=
@z
