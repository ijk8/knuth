\datethis
\let\xor=\oplus
@*Intro. This program is the first of a series in which I shall
try to find the optimum way to compute as many of the Boolean 5-variable
functions as I can.

There are 616,126 equivalence classes of such functions, under permutation
and/or complementation of variables and of the function value itself.
I want to represent each class by its smallest truth table.
The nice algorithm of exercise 7.2.1.2--20 makes it easy to run through
all functions in a class.
(When $n=5$ there are roughly 7000 times as many Boolean functions as classes;
the stated scheme allows me to fit everything in the memory of my trusty old
computer.)

This program simply makes a list of all the classes, and puts them into
a hash table for ready retrieval. It writes out the completed hash table to a
binary file, \.{/tmp/5chains0.db}, which can conveniently be read and
modified by subsequent programs in this series.

@d n 5
@d nfactorial 120
@d nnn (nfactorial<<n) /* $2^nn!$, the number of $n$-cube symmetries */
@d hashprime 859987 /* range of hash function */
@d hashsize 1000000 /* total size of hash table */
 /* |hashprime| is about 86\% of |hashsize|; see exercise 6.4--43 */
@d mult 0x61c88647 /* $\approx 2^{32}\!/\phi^2$, Eq.~ 6.4--(7) */
@d head(l) (&hash[hashsize-16+l]) /* sixteen list heads */

@c
#include <stdio.h>
char delta[nnn]; /* for symmetries via exercise 7.2.1.2--20 */
typedef unsigned int truthtab;
typedef struct class_struct {
  truthtab tt; /* smallest truth table */
  short size; /* the number of elements in the class */
  short cost; /* fewest steps to reach this class with minimum-memory scheme */
  int history1,history2; /* how we reached that cost */
  int parent; /* the historic progenitor */
  int prv, nxt; /* links for list processing */
  int lnk; /* link for coalesced hashing (Algorithm 6.4C) */
} fclass;
fclass hash[hashsize]; /* master list of all classes */
int count; /* this many classes found */
FILE *outfile;

main()
{
  register int i,j,k,d,s,auts;
  register truthtab t,tt;
  register fclass *c;
  @<Initialize the |delta| table@>;
  @<Find all the classes@>;
  @<Output the table@>;
}

@ @<Initialize the |delta| table@>=
delta[0]=-1;
for (d=1,k=n;k;d*=k+k,k--) {
  for (j=d,i=k-1,s=-1;j<nnn;j+=d) {
    delta[j]=i, i+=s;
    if (i<0) i=s=1;
    else if (i>k) i=k-1,s=-1;
  }
}  

@ Links in the |hash| database are integers rather than pointers,
because other programs will read this database into unknown locations.
Therefore I'm writing `|link(c)|' instead of `|c->link|', and
`|setlink(c,x)|' instead of `|c->link=x|'.

@d prev(c) (hash+(c)->prv)
@d next(c) (hash+(c)->nxt)
@d link(c) (hash+(c)->lnk)
@d setprev(c,x) (c)->prv=(x)-hash
@d setnext(c,x) (c)->nxt=(x)-hash
@d setlink(c,x) (c)->lnk=(x)-hash

@ Here's how we go from a truth table to the table entry for its class.
The hash table has the possibly useful property that |cc=link(c)|
and |c->lnk!=0| implies |cc->tt>c->tt|.

For simplicity we set each |cost| to 15, which is an upper bound.

@d full_shift (1<<n)
@d half_shift (1<<(n-1))
@d quart_shift (1<<(n-2))
@d eighth_shift (1<<(n-3))
@d xvi_shift (1<<(n-4))
@d xxxii_shift (1<<(n-5))
@d mask ((truthtab)((1<<full_shift)-1)) /* $2^{2^n}-1$ */
@d half_mask ((1<<half_shift)-1)
@d quart_mask ((1<<quart_shift)-1)
@d eighth_mask ((1<<eighth_shift)-1)
@d xvi_mask ((1<<xvi_shift)-1)
@d xxxii_mask ((1<<xxxii_shift)-1)
@d infty 999

@<Find all the classes@>=
s=hashsize-16; /* reservoir pointer */
for (j=0;j<16;j++) setprev(head(j),head(j)), setnext(head(j),head(j));
for (tt=0;tt<=(mask>>1);tt++) {
  t=tt, auts=1;
  for (j=1;j<nnn;j++) {
    switch (delta[j]) {
      @<Cases to move to the next truth table@>@;
    }
    if (t<=tt) {
      if (t==tt) auts++;
      else goto nogood; /* not canonical */
    }
  }
  count++; /* |tt| is smallest in its class */
  printf("%d: %08x (%d aut%s)\n",count,tt,auts,auts==1?"":"s");
  c=&hash[(tt^(mult*tt))%hashprime];
  if (c->parent) { /* this position is occupied */
    while (c->lnk) c=link(c);
    for (s--;hash[s].parent;s--);
    setlink(c,&hash[s]), c=link(c);
  }
  c->tt=tt, c->cost=15, c->size=7680/auts;
  c->parent=-1;
  setnext(c,head(15)), setprev(c,prev(head(15)));
  setprev(next(c),c), setnext(prev(c),c);
nogood: continue;
}

@ @<Cases to move to the next truth table@>=
case 0: t=(t<<half_shift)+(t>>half_shift);
  if (n<5) t&=mask;
case -1:@+ if (t>(mask>>1)) t^=mask; /* complement so that $f(0,\ldots,0)=0$ */
  break;
case 1: d=(t^(t>>quart_shift))&(quart_mask<<quart_shift);
  t^=d+(d<<quart_shift);
  break;
case 2: d=(t^(t>>eighth_shift))&((eighth_mask<<eighth_shift)*(mask/half_mask));
  t^=d+(d<<eighth_shift);
  break;
case 3: d=(t^(t>>xvi_shift))&((xvi_mask<<xvi_shift)*(mask/quart_mask));
  t^=d+(d<<xvi_shift);
  break;
case 4: d=(t^(t>>xxxii_shift))&((xxxii_mask<<xxxii_shift)*(mask/eighth_mask));
  t^=d+(d<<xxxii_shift);
  break;

@ @<Output the table@>=
outfile=fopen("/tmp/5chains0.db","wb");
fprintf(stderr,"%dx%d bytes written on /tmp/5chains0.db\n",
       sizeof(fclass),fwrite(hash,sizeof(fclass),hashsize,outfile));

@*Index.
