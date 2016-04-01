\datethis
@*Intro. I'm hurriedly experimenting with a new(?) way to explore the
complexity of 5-variable Boolean functions. Namely, I calculate the
``footprint'' of each function, the set of all first steps by which I
know how to evaluate the function in $k$ steps. Then, if the footprints
of $f$ and $g$ overlap, I can compute $f\circ g$ in
${\rm cost}(f)+{\rm cost}(g)$ steps.

(This program was hacked from {\mc FCHAINS4}. I don't have time to
do a complete test, so I'm only going up to cost 6. That means there
fewer than 5 million functions to consider, instead of $2^{31}$.)

@d mult 0x61c88647 /* $\approx 2^{32}\!/\phi^2$, Eq.~ 6.4--(7) */
@d fhprime 8333329

@c
#include <stdio.h>
typedef unsigned int truthtab;
typedef struct node_struct {
  truthtab tt; /* truth table */
  int footprint1,footprint2;
  int cost;
  struct node_struct *prev, *next;
} node;
node funchash[fhprime];
node head[8];
node zeronode;
char buf[100]; /* lines of input */
truthtab x[6];
truthtab ttt; /* truth table found in input line */
@<Subroutines@>@;
main()
{
  register int k,r,t,u,uu;
  register node *p,*q,*pp;
  @<Initialize the tables@>;
  for (r=2;r<=6;r++)
    for (k=(r-1)>>1;k>=0;k--)
      @<Combine all functions of costs |k| and |r-1-k|@>;
  @<Answer queries@>;
}

@ @<Sub...@>=
node *lookup(truthtab tt)
{
  register node *c;
  if (tt==0) return &zeronode;
  for (c=&funchash[(tt^(mult*tt))%fhprime];c->tt;c--) {
    if (c->tt==tt) goto found;
    if (c==&funchash[0]) c=&funchash[fhprime];
  }
  c->tt=tt, c->cost=15;
found: return c;
}
  
@ @<Combine all functions of costs |k| and |r-1-k|@>=
for (p=head[k].next;p->footprint1>=0;p=p->next)
  for (q=head[r-1-k].next;q->footprint1>=0;q=q->next) {
    u=p->footprint1 | q->footprint1, uu=p->footprint2 | q->footprint2;
    if ((p->footprint1 & q->footprint1) ||
        (p->footprint2 & q->footprint2)) @<Try for breakthru@>@;
    else @<Try for new function@>;
  }

@ @d fun(p) ((p)->tt)

@<Try for new function@>=
{
  t=fun(p)&fun(q), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r|@>;
  t=fun(p)&(~fun(q)), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r|@>;
  t=(~fun(p))&fun(q), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r|@>;
  t=fun(p)|fun(q), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r|@>;
  t=fun(p)^fun(q), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r|@>;
}

@ @<Update the table for cost |r|@>=
{
  if (pp->cost>r) {
    if (pp->cost!=15)  pp->next->prev=pp->prev, pp->prev->next=pp->next;
    pp->cost=r, pp->footprint1=pp->footprint2=0;
    pp->next=head[r].next, pp->prev=&head[r];
    pp->next->prev=pp, pp->prev->next=pp;
  }
  pp->footprint1|=u, pp->footprint2|=uu;
}

@ @<Try for breakthru@>=
{
  t=fun(p)&fun(q), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r-1|@>;
  t=fun(p)&(~fun(q)), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r-1|@>;
  t=(~fun(p))&fun(q), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r-1|@>;
  t=fun(p)|fun(q), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r-1|@>;
  t=fun(p)^fun(q), pp=lookup(t);
  if (pp->cost>=r) @<Update the table for cost |r-1|@>;
}

@ This code is not executed when $k=0$, because |q|'s footprint is zero
in that case.

@<Update the table for cost |r-1|@>=
{
  if (pp->cost>r-1) {
    if (pp->cost!=15) pp->next->prev=pp->prev, pp->prev->next=pp->next;
    pp->cost=r-1, pp->footprint1=pp->footprint2=0;
    pp->next=head[r-1].next, pp->prev=&head[r-1];
    pp->next->prev=pp, pp->prev->next=pp;
  }
  pp->footprint1|=u, pp->footprint2|=uu;
}

@ @<Initialize the tables@>=
for (k=0;k<=6;k++)
  head[k].footprint1=-1, head[k].next=head[k].prev=&head[k];
@<Initialize the functions of cost 0@>;
@<Initialize the functions of cost 1@>;

@ I don't put the zero function in the list for cost 0.

@<Initialize the functions of cost 0@>=
for (k=1;k<=5;k++) {
  x[k]=(truthtab)0xffffffff/((1<<(1<<(5-k)))+1);
  p=lookup(x[k]);
  p->cost=0;
  p->next=head[0].next, p->prev=&head[0];
  p->next->prev=p, p->prev->next=p;
}  

@ @<Initialize the functions of cost 1@>=
u=1,uu=0;
for (k=1;k<5;k++) for (r=k+1;r<=5;r++) {
  t=x[k]&x[r]; @<Update for cost 1@>;
  t=x[k]&(~x[r]); @<Update for cost 1@>;
  t=(~x[k])&x[r]; @<Update for cost 1@>;
  t=x[k]|x[r]; @<Update for cost 1@>;
  t=x[k]^x[r]; @<Update for cost 1@>;
}

@ @<Update for cost 1@>=
p=lookup(t);
printf("%04x has footprint %07x%07x\n",t,uu,u);
p->cost=1, p->footprint1=u, p->footprint2=uu;
u<<=1, uu<<=1;
if (u==0x10000000) u=0, uu=1;
p->next=head[1].next, p->prev=&head[1];
p->next->prev=p, p->prev->next=p;

@ @<Answer queries@>=
while (1) {
  printf("Truth table (hex): ");
  fflush(stdout);
  if (!fgets(buf,100,stdin)) break;
  if (sscanf(buf,"%x",&ttt)!=1) break;
  p=lookup(ttt);
  printf("%08x has cost %d and footprint %07x%07x\n",
        ttt,p->cost,p->footprint2,p->footprint1);
}

@*Index.
