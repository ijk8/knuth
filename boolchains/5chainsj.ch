@x change file for 5chainsi, rethinking the order of operations
  @<Try all top-down combinations@>;
  @<Try all bottom-up combinations@>;
  @<Input the special cases@>;
@y
  @<Input the special cases@>;
  r++;
  count=0;
  @<List the items already known to be at distance |r|@>;
  @<Try all top-down combinations@>;
  @<Try all bottom-up combinations@>;
@z
@x
for (k=0;k<15;k++) for (c=next(head(k));c->parent;c=next(c)) {
@y
for (k=0;k<=r+2;k++) {
 printf("Warming up dist %d...\n",k); fflush(stdout);
  for (c=next(head(k));c->parent;c=next(c)) {
@z
@x
}
@y
 }
}
@z
