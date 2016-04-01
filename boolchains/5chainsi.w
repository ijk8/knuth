\datethis
\let\xor=\oplus
@*Intro. This program is part of a series in which I shall
try to find the optimum way to compute as many of the Boolean 5-variable
functions as I can. It updates a database of such functions that
was previously computed, so as to cover all functions that can
be evaluated in at most $r$ steps.

There are three command-line parameters in addition to the standard
input file. In a typical run,
$$\.{5chainsi 5chains6.db 7 5chains7.db < 5chains7.in}$$
would input `\.{5chains6.db}', a database that is correct up to $r=6$,
and it would augment the data for one more step, finally putting the
results into a new database `\.{5chains7.db}'.

Three kinds of $r$-step computations are possible:
(1)~A {\it top-down\/} calculation computes
$f(x_1,\ldots,x_5)=g(x_1,\ldots,x_5)\circ h(x_1,\ldots,x_5)$,
where $g$ and~$h$ are previously known to take $k$ and $r-1-k$ steps
when computed independently. 
(2)~A {\it bottom-up\/} calculation computes, for example,
$f(x_1,x_2,\ldots,x_5)=g(x_1\circ x_2,x_2,\ldots,x_5)$, where
$g$ is known to be doable in $r-1$ steps.
(3)~A special computation simply is an assertion that an $r$-step
trick exists for $f(x_1,\ldots,x_5)$; other programs are
responsible for discovering such tricks.

If the input database is correct for all computations of length less
than~$r$, and if all $r$-step computations are obtainable either
top-down, bottom-up, or by one of the tricks in the standard input,
then this program will output a database that is correct for
computations of length $r$~or less. But if the standard input doesn't
contain all such tricks, the output database will only give upper bounds.

This program also considers auxiliary types of bottom-up computations
such as $f(x_1,x_2,x_3,x_4,x_5)=g(x_1\land x_2,x_1\lor x_2,x_3,x_4,x_5)$;
it records that fact that $f$ can be computed in at most $r+1$ steps
if $g$ can be computed in~$r-1$. Information such as this can be used
to reduce the number of special cases that need to be tried.
(See the {\mc SCHAINS} program; this feature allows us to
restrict consideration to special chains that aren't ``tame.'')

A special version of this program, called {\mc 5CHAINS1}, primes the
pump by going from \.{5chains0.db} to \.{5chains5.db} (or even to
\.{5chains15.db} if desired, but without considering any special chains).

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
char *dist; /* base of a table of distances */
@<Subroutines@>@;
int rr; /* the value of |r| on the command line */
int count; /* this many classes found at distance |r| */
FILE *infile, *outfile;
char buf[100]; /* lines of input */
truthtab ttt; /* truth table scanned from input */
int kk; /* serial number scanned from input */

main(int argc,char *argv[])
{
  register int i,j,k,d,r,s,auts;
  register truthtab t,tt;
  register fclass *c,*cc,*ccc;
  @<Check the command line@>;
  @<Initialize the |delta| table@>;
  @<Make the |dist| table@>;
  @<List the items already known to be at distance |r|@>;
  @<Try all top-down combinations@>;
  @<Try all bottom-up combinations@>;
  @<Input the special cases@>;
  @<Output the new database@>;
}

@ @<Check the command line@>=
if (argc!=4 || sscanf(argv[2],"%d",&rr)!=1) {
  fprintf(stderr,"Usage: %s input.db r output.db < specials\n",argv[0]);
  exit(-1);
}
r=rr;
infile=fopen(argv[1],"rb");
if (!infile) {
  fprintf(stderr,"I can't open file %s for reading!\n", argv[1]);
  exit(-2);
}
if (fread(hash,sizeof(fclass),hashsize,infile)!=hashsize) {
  fprintf(stderr,"I couldn't read file %s successfully!\n", argv[1]);
  exit(-3);
}
outfile=fopen(argv[3],"wb");
if (!outfile) {
  fprintf(stderr,"I can't open file %s for writing!\n", argv[3]);
  exit(-4);
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

@ I don't declare |dist| as an array, because the \CEE/ assembler/loader
requires arrays to have less than $2^{31}$ bytes.

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
@d xx(k) (mask/((1<<(1<<(n-k)))+1)) /* the truth table of $x_k$ */

@<Make the |dist|...@>=
dist=(char*)malloc((unsigned int)(1<<((1<<n)-1)));
if (!dist) {
  fprintf(stderr,"I couldn't allocate the dist array!\n");
  exit(-5);
}
for (j=0;j<(1<<((1<<n)-1))-1;j++) dist[j]=15;
dist[j]=15; /* we need to be sure that |j| stays nonnegative */
for (k=0;k<15;k++) for (c=next(head(k));c->parent;c=next(c)) {
  t=c->tt;
  for (j=0;j<nnn;j++) {
    switch (delta[j]) {
      @<Cases to move to the next truth table@>@;
    }
    dist[t]=k;
  }
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
use |classify| instead of |lookup|.

@<Sub...@>=
fclass *classify(register truthtab t)
{
  register int j;
  register truthtab tt,d;
  tt=t;
  for (j=1;j<nnn;j++) {
    switch (delta[j]) {
      @<Cases to move to the next truth table@>@;
    }
    if (t<tt) tt=t;
  }
  return lookup(tt);
}

@ Another subroutine is used when we discover how to decrease the cost
of a Boolean function.

@<Sub...@>=
void setcost(fclass *c, int r)
{
  register int j;
  register truthtab t,d;
  register fclass *pr,*nx;
  pr=prev(c), nx=next(c);
  setnext(pr,nx), setprev(nx,pr);
  pr=prev(head(r)), nx=head(r);
  setprev(c,pr), setnext(c,nx);
  setnext(pr,c), setprev(nx,c);
  c->cost=r;
  for (t=c->tt,j=0;j<nnn;j++) {
    switch (delta[j]) {
      @<Cases to move to the next truth table@>@;
    }
    dist[t]=r;
  }
}  

@ @<List the items already known to be at distance |r|@>=
printf("Classes at distance %d:\n",r);
for (c=next(head(r));c->parent;c=next(c)) {
  count++;
  printf("%d: %08x\n",count,c->tt);
}

@ @<Try all top-down combinations@>=
for (k=0;k<=r-1-k;k++) {
  for (cc=next(head(r-1-k)); cc->parent; cc=next(cc))
    for (c=next(head(k)); c->parent; c=next(c))
      for (t=c->tt,j=0;j<nnn;j++) {
        switch (delta[j]) {
          @<Cases to move to the next truth table@>@;
        }
        @<Try combining |cc->tt| with |t|@>;
      }
}

@ @<Try combining |cc->tt| with |t|@>=
if (dist[cc->tt&t]>r) {
  ccc=classify(cc->tt&t);
  setcost(ccc,r);
  ccc->history1=(j<<4)+8, ccc->history2=cc->tt, ccc->parent=c-hash;
  count++;
  printf("%d: %08x from %08x&%08x [%08x(%d)]\n",
               count,ccc->tt,cc->tt,t,c->tt,j);
}
if (dist[cc->tt&~t]>r) {
  ccc=classify(cc->tt&~t);
  setcost(ccc,r);
  ccc->history1=(j<<4)+9, ccc->history2=cc->tt, ccc->parent=c-hash;
  count++;
  printf("%d: %08x from %08x\\%08x [%08x(%d)]\n",
               count,ccc->tt,cc->tt,t,c->tt,j);
}
if (dist[t&~cc->tt]>r) {
  ccc=classify(t&~cc->tt);
  setcost(ccc,r);
  ccc->history1=(j<<4)+10, ccc->history2=cc->tt, ccc->parent=c-hash;
  count++;
  printf("%d: %08x from %08x/%08x [%08x(%d)]\n",
               count,ccc->tt,cc->tt,t,c->tt,j);
}
if (dist[cc->tt|t]>r) {
  ccc=classify(cc->tt|t);
  setcost(ccc,r);
  ccc->history1=(j<<4)+11, ccc->history2=cc->tt, ccc->parent=c-hash;
  count++;
  printf("%d: %08x from %08x|%08x [%08x(%d)]\n",
               count,ccc->tt,cc->tt,t,c->tt,j);
}
if (dist[cc->tt^t]>r) {
  ccc=classify(cc->tt^t);
  setcost(ccc,r);
  ccc->history1=(j<<4)+12, ccc->history2=cc->tt, ccc->parent=c-hash;
  count++;
  printf("%d: %08x from %08x^%08x [%08x(%d)]\n",
               count,ccc->tt,cc->tt,t,c->tt,j);
}

@ @<Try all bottom-up combinations@>=
for (c=next(head(r-1)); c->parent; c=next(c))
  for (t=c->tt,j=0;j<nnn;j++) {
    switch (delta[j]) {
      @<Cases to move to the next truth table@>@;
    }
    @<Try variants reachable from truth table |t|@>;
  }

@ @<Try variants reachable from truth table |t|@>=
@<Try replacing $x_1$ by $x_1\land x_2$@>;
@<Try replacing $x_1$ by $x_1\xor x_2$@>;
@<Try replacing $x_1$ by $x_2\land x_3$@>;
@<Try replacing $x_1$ by $x_2\xor x_3$@>;
@<Try replacing $(x_1,x_2)$ by $(x_1\land x_2,x_1\lor x_2)$@>;
@<Try replacing $(x_1,x_2)$ by $(x_1\land x_2,x_1\xor x_2)$@>;

@ @<Try replacing $x_1$ by $x_1\land x_2$@>=
tt=t^((t^(t>>half_shift))&(quart_mask<<quart_shift));
if (dist[tt]>r) {
  cc=classify(tt);
  setcost(cc,r);
  cc->history1=(j<<4), cc->parent=c-hash;
  count++;
  printf("%d: %08x from %08x(%d)=%08x 1&2\n",count,cc->tt,c->tt,j,t);
}

@ @<Try replacing $x_1$ by $x_1\xor x_2$@>=
tt=t^((t^(t>>half_shift)^(t<<half_shift))&xx(2));
if (dist[tt]>r) {
  cc=classify(tt);
  setcost(cc,r);
  cc->history1=(j<<4)+1, cc->parent=c-hash;
  count++;
  printf("%d: %08x from %08x(%d)=%08x 1^2\n",count,cc->tt,c->tt,j,t);
}

@ @<Try replacing $x_1$ by $x_2\land x_3$@>=
tt=t^((t^(t>>half_shift)^(t<<half_shift))&(xx(1)^(xx(2)&xx(3))));
if (dist[tt]>r) {
  cc=classify(tt);
  setcost(cc,r);
  cc->history1=(j<<4)+2, cc->parent=c-hash;
  count++;
  printf("%d: %08x from %08x(%d)=%08x 2&3\n",count,cc->tt,c->tt,j,t);
}

@ I think I can prove this step is useless, because of my knowledge of
the case $n=4$. (Indeed, I think the previous step improves
the cost of just one more class.) But computers sometimes surprise me.

@<Try replacing $x_1$ by $x_2\xor x_3$@>=
tt=t^((t^(t>>half_shift)^(t<<half_shift))&(xx(1)^(xx(2)&xx(3))));
if (dist[tt]>r) {
  cc=classify(tt);
  setcost(cc,r);
  cc->history1=(j<<4)+3, cc->parent=c-hash;
  count++;
  printf("%d, %08x from %08x(%d)=%08x 2^3\n",count,cc->tt,c->tt,j,t);
}

@ Here's a second-order bottom-up method.

@<Try replacing $(x_1,x_2)$ by $(x_1\land x_2,x_1\lor x_2)$@>=
tt=t^((t^(t>>quart_shift))&(quart_mask<<quart_shift));
if (dist[tt]>r+1) {
  cc=classify(tt);
  setcost(cc,r+1);
  cc->history1=(j<<4)+4, cc->parent=c-hash;
  printf("(%08x from %08x(%d)=%08x 1&2,1|2 has cost %d)\n",
      cc->tt,c->tt,j,t,r+1);
}

@ I'm not sure if this is useful, but I couldn't rule it out.

@<Try replacing $(x_1,x_2)$ by $(x_1\land x_2,x_1\xor x_2)$@>=
tt=t^((t^(t>>quart_shift))&half_mask);
if (dist[tt]>r+1) {
  cc=classify(tt);
  setcost(cc,r+1);
  cc->history1=(j<<4)+5, cc->parent=c-hash;
  printf("(%08x from %08x(%d)=%08x 1&2,1^2 has cost %d)\n",
      cc->tt,c->tt,j,t,r+1);
}

@ @<Input the special cases@>=
while (fgets(buf,100,stdin)) {
  if (sscanf(buf,"%d: %x",&kk,&ttt)!=2 || ((c=lookup(ttt))==NULL)) {
    printf("Eh? I'm ignoring this input line: %s",buf);
    continue;
  }
  if (c->cost<=r) {
    printf("Ignoring input line because the cost is already %d: %s",
                   c->cost,buf);
    continue;
  }
  setcost(c,r);
  count++;
  printf("%d: %s",count,buf);
  c->parent=-2;
  c->history1=kk;
}  

@ @<Output the new...@>=
fprintf(stderr,"%dx%d bytes written on %s\n",
       sizeof(fclass),fwrite(hash,sizeof(fclass),hashsize,outfile),argv[3]);

@*Index.
