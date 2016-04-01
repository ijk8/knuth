\datethis
\let\xor=\oplus
@*Intro. This program is part of a series in which I'm trying
to find the optimum way to compute as many of the Boolean 5-variable
functions as I can. It inputs a database produced by one of the
other programs, and it gives a symbolic explanation of how any
given function  was computed.

The database is specified as a command-line parameter;
the program itself is interactive, prompting the user for
the truth tables that are supposed to be explained.

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
#include <stdlib.h>
@h
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
char perm[nnn][8]; /* table of signed permutations */
char ip[n+1]; /* an inverse permutation */
int jpos,comp; /* outputs of the |classify| routine */
@<Subroutines@>@;
FILE *infile;
char buf[100]; /* lines of input */
truthtab ttt; /* truth table found in input line */
char opsym[]={'&','\\','/','|','^'}; /* symbolic representations */

main(int argc,char *argv[])
{
  register int i,j,k,d,s,cmp;
  register truthtab t,tt;
  register fclass *c;
  @<Check the command line@>;
  @<Initialize the |delta| table and other tables@>;
  while (1) {
    printf("Truth table (hex): ");
    fflush(stdout);
    if (!fgets(buf,100,stdin)) break;
    if (sscanf(buf,"%x",&ttt)!=1) break;
    @<Explain the function |ttt|@>;
  }
}

@ @<Check the command line@>=
if (argc!=2) {
  fprintf(stderr,"Usage: %s input.db\n",argv[0]);
  exit(-1);
}
infile=fopen(argv[1],"rb");
if (!infile) {
  fprintf(stderr,"I can't open file %s for reading!\n", argv[1]);
  exit(-2);
}
if (fread(hash,sizeof(fclass),hashsize,infile)!=hashsize) {
  fprintf(stderr,"I couldn't read file %s successfully!\n", argv[1]);
  exit(-3);
}

@ @<Initialize the |delta| table...@>=
delta[0]=-1;
for (d=1,k=n;k;d*=k+k,k--) {
  for (j=d,i=k-1,s=-1;j<nnn;j+=d) {
    delta[j]=i, i+=s;
    if (i<0) i=s=1;
    else if (i>k) i=k-1,s=-1;
  }
}  

@ In order to decode the internal representation of a function,
we prepare a table of the signed permutations used to generate all
members of an equivalence class.

@<Init...@>=
for (k=1;k<=n;k++) perm[0][k]=k;
for (j=1;j<nnn;j++) {
  for (k=1;k<=n;k++) perm[j][k]=perm[j-1][k];
  if (!delta[j]) perm[j][1]=-perm[j][1];
  else k=perm[j][delta[j]], perm[j][delta[j]]=perm[j][delta[j]+1],
         perm[j][delta[j]+1]=k;
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

@ Here's the basic hash-table lookup for the databases of interest.

@<Sub...@>=
fclass *lookup(truthtab tt)
{
  register fclass *c;
  for (c=&hash[(tt^(mult*tt))%hashprime];c->parent;c=link(c)) {
    if (c->tt==tt) return c;
    if (c->tt>tt || !(c->lnk)) return NULL;
  }
  return NULL;
}
  
@ If we don't know the class representative of a truth table, we
use |classify| instead of |lookup|. This subroutine also sets
global variable |jpos| to indicate the signed permutation of interest.

@<Sub...@>=
fclass *classify(register truthtab t)
{
  register int j,cmp;
  register truthtab tt,d;
  tt=mask,cmp=0;
  for (j=0;j<nnn;j++) {
    switch (delta[j]) {
      @<Cases to move to the next truth table@>@;
    }
    if (t<tt) tt=t,jpos=j,comp=cmp;
  }
  return lookup(tt);
}

@ @d full_shift (1<<n)
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
@d xx(k) (mask/((1<<(1<<(n-k)))+1)) /* the truth table of $x_k$ */

@<Cases to move to the next truth table@>=
case 0: t=(t<<half_shift)+(t>>half_shift);
  if (n<5) t&=mask;
case -1:@+ if (t>(mask>>1)) t^=mask,cmp^=1;
             /* complement so that $f(0,\ldots,0)=0$ */
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

@ @<Explain the function |ttt|@>=
c=classify(ttt);
printf("%08x is function %s%08x(%+d%+d%+d%+d%+d)\n",
       ttt, comp?"~":"", c->tt,
       perm[jpos][1],perm[jpos][2],perm[jpos][3],perm[jpos][4],perm[jpos][5]);
printf("%08x has class size %d, cost %d, and is computed thus:\n",
          c->tt,c->size,c->cost);
if (c->parent<0) {
  if (c->parent==-1) printf("  (primitive)\n");
  else printf(" use special chain number %d\n",c->history1);
}@+else @<Explain how to compute |c->tt|@>;

@ @d topdown(x) tt=x;@+printf("%08x=%08x%c%08x\n",
             x,c->history2,opsym[c->history1&0x7],t);@+break
@d botup(x,m) tt=x;@+printf("%08x=%08x(%s,3,4,5)\n",x,t,m);@+break

@<Explain how to compute |c->tt|@>=
{
  i=c->history1>>4;
  t=hash[c->parent].tt;
  for (j=1,cmp=0;j<=i;j++)
    switch (delta[j]) {
      @<Cases to move to the next truth table@>@;
    }
  for (k=1;k<=n;k++)
    if (perm[i][k]>0) ip[perm[i][k]]=k;
    else ip[-perm[i][k]]=-k;
  printf("first compute %08x=%s%08x(%+d%+d%+d%+d%+d)\nthen ",
            t,cmp?"~":"",hash[c->parent].tt,ip[1],ip[2],ip[3],ip[4],ip[5]);
  switch((c->history1)&0xf) {
case 0: botup(t^((t^(t>>half_shift))&(quart_mask<<quart_shift)),"1&2,2");
case 1: botup(t^((t^(t>>half_shift)^(t<<half_shift))&xx(2)),"1^2,2");
case 2: botup(t^((t^(t>>half_shift)^(t<<half_shift))&(xx(1)^(xx(2)&xx(3)))),
          "2&3,3");
case 3: botup(t^((t^(t>>half_shift)^(t<<half_shift))&(xx(1)^(xx(2)&xx(3)))),
          "2^3,3");
case 4: botup(t^((t^(t>>quart_shift))&(quart_mask<<quart_shift)),"1&2,1|2");
case 5: botup(t^((t^(t>>quart_shift))&half_mask),"1&2,1^2");
case 8: topdown(c->history2&t);
case 9: topdown(c->history2&(~t));
case 10: topdown(~(c->history2)&t);
case 11: topdown(c->history2|t);
case 12: topdown(c->history2^t);
default: printf("unknown case!\n");
  }
  c=classify(tt);
  if (tt!=c->tt) {
    for (k=1;k<=n;k++)
      if (perm[jpos][k]>0) ip[perm[jpos][k]]=k;
      else ip[-perm[jpos][k]]=-k;
    printf("and %08x=%s%08x(%+d%+d%+d%+d%+d)\n",c->tt,comp?"~":"",tt,
       ip[1],ip[2],ip[3],ip[4],ip[5]);
  }
}

@*Index.
