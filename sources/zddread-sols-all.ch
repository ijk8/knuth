@x THIS IS A CHANGE FILE FOR "bddread.w"
With change files I can adapt it to other uses.
@y
Here I compute all the solutions, using ZDD conventions.
@z
@x
@d memsize 200000 /* this many nodes */
@d varsize 128 /* this many variables */
@d bdds 2 /* this many BDDs */
@y
@d memsize 40000000 /* this many nodes */
@d varsize 512 /* this many variables */
@d bdds 1 /* this many BDDs */
@z
@x
node* mem[bdds];
@y
node* mem[bdds];
int present[varsize];
int stack[varsize];
int stackptr;
int serial;
@z
@x
          k++,mem[r][i1].v=i2, mem[r][i1].lo=i3, mem[r][i1].hi=i4;
@y
          k++,mem[r][i1].v=i2, mem[r][i1].lo=i3, mem[r][i1].hi=i4;
          present[i2]=1;
@z
@x
@ @<Sub...@>=

@ @<Do our thing@>=
@y
@ First, a recursive subroutine.

@d var(p) mem[0][p].v

@<Sub...@>=
void printpaths(int p) {
  register int k,q;
  if (p<=1) {
    printf("%d:",serial);
    for (q=0;q<stackptr;q++) printf(" %d",stack[q]);
    printf("\n");
    serial++;
    return;
  }
  q=mem[0][p].lo;
  if (q) printpaths(q);
  q=mem[0][p].hi;
  if (q) {
    stack[stackptr++]=mem[0][p].v;
    printpaths(q);
    stackptr--;
  }
}

@ @<Do our thing@>=
for (j=k=0;j<varsize;j++) if (present[j]) k++;
fprintf(stderr,"There are %d variables.\n",k);
mem[0][0].v=mem[0][1].v=varsize;
if (root[0]) printpaths(root[0]);
@z
