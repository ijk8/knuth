\datethis
\let\xor=\oplus
@*Intro. This program is part of a series in which I shall
try to find the optimum way to compute as many of the Boolean 5-variable
functions as I can. It checks a given set of special chains
to see if they lead to any improvements over the complexities
that are recorded in a given database. It outputs the names of
classes for which improvements are found, using a format that
can be used for standard input to {\mc 5CHAINSI}.

There are three command-line parameters in addition to the standard
input file. In a typical run,
$$\.{5chainst 5chains7.db 7 5chains7.in < schains5-7.out}$$
would input `\.{5chains7.db}', a database that is correct up to $r=7$,
except possibly for special 7-step tricks. In the text file
\.{5chains7.in}, it reports any improvements
that correspond to chains in the file \.{schains5-7.out}, where the
latter file has been output by the program {\mc SCHAINS}.

The value of |r| is actually a compile-time parameter (as it is in
{\mc SCHAINS}), because I'm trying to gain speed. The inner loop
of this program will be executed trillions of times; thus I won't
mind recompiling for a few different values of~|r|.

@d n 5
@d nfactorial 120
@d r 7
@d nnn (nfactorial<<n) /* $2^nn!$, the number of $n$-cube symmetries */
@d hashprime 859987 /* range of hash function */
@d hashsize 1000000 /* total size of hash table */
 /* |hashprime| is about 86\% of |hashsize|; see exercise 6.4--43 */
@d mult 0x61c88647 /* $\approx 2^{32}\!/\phi^2$, Eq.~ 6.4--(7) */
@d head(l) (&hash[hashsize-16+l]) /* sixteen list heads */

@c
#include <stdio.h>
#include <string.h>
#include <time.h>
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
char *dist; /* base of a table of distances */
@<Subroutines@>@;
int rr; /* the value of |r| on the command line */
int count,grandcount; /* this many classes found at distance |r| */
FILE *infile,*outfile;
char buf[100]; /* lines of input */
truthtab x[16],y[16],z[16]; /* truth tables */
char jop[16],kop[16]; /* chain operands */
char op[16]; /* chain operators */
char opsym[]={'&','\\','/','|','+'}; /* symbolic representations */
char regsym[]={'0','1','2','3','4','5','6','7','8','9',@|
  'a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p',
  'q','r','s','t','u','v','w','x','y','z'};

main(int argc,char *argv[])
{
  register int i,j,k,d,s,auts;
  register truthtab t,tt;
  register fclass *c,*cc,*ccc;
  register char *p;
  @<Check the command line@>;
  @<Initialize the |delta| table and other tables@>;
  @<Make the |dist| table@>;
  @<Process the special chains@>;
  printf("Altogether %d tricks written on file %s\n",grandcount,argv[3]);
}

@ @<Check the command line@>=
if (argc!=4 || sscanf(argv[2],"%d",&rr)!=1) {
  fprintf(stderr,"Usage: %s input.db r specials < schains\n",argv[0]);
  exit(-1);
}
if (rr!=r) {
  fprintf(stderr,"Please recompile me: I only accept the value r=%d!\n",r);
  exit(-69);
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
outfile=fopen(argv[3],"w");
if (!outfile) {
  fprintf(stderr,"I can't open file %s for writing!\n", argv[3]);
  exit(-4);
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

In this program, |dist[t]| is 1 if and only if no way is known (as yet)
to compute |t| with |r| or fewer steps.

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
for (j=0;j<(1<<((1<<n)-1))-1;j++) dist[j]=1;
dist[j]=1;
for (k=0;k<=r;k++) for (c=next(head(k));c->parent;c=next(c)) {
  t=c->tt;
  for (j=0;j<nnn;j++) {
    switch (delta[j]) {
      @<Cases to move to the next truth table@>@;
    }
    dist[t]=0;
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

The list updating here isn't really important, except for changes
to |dist|. But I've retained it just to be tidy. No harm is done
if |setcost| is performed twice on the same class.

@<Sub...@>=
void setcost(fclass *c)
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
    dist[t]=0;
  }
}  

@ @<Process the special chains@>=
while (fgets(buf,100,stdin)) {
  clock_t timer;
  if (strchr(buf,'*')) continue; /* ignore starred lines */
  count=0, timer=clock();
  @<Parse the input line, setting the |jop| and |kop| tables;
     |goto done| if there's a problem@>;
  @<Run through $5^r$ sequences, looking for cost savings@>;
  printf("(%d) %d from %s",(int)(clock()-timer),count,buf);
done: continue;
}

@ @d abort(m) {
    printf("input line not understood (%s!):\n %s",m,buf);
    goto done;
  }

@<Parse the input line...@>=
p=strchr(buf,':');
if (!p) abort("no colon");
for (p+=2,j=n+1; *p; p+=2,j++) {
  if (*p>='1' && *p<='9') jop[j]=*p-'0';
  else if (*p>='a' && *p<='z') jop[j]=*p+10-'a';
  else abort("nondigit");
  p++;
  if (*p>='1' && *p<='9') kop[j]=*p-'0';
  else if (*p>='a' && *p<='z') kop[j]=*p+10-'a';
  else abort("nondigit");
}
if (j<n+1+r) abort("chain too short");
if (j>n+1+r) abort("chain too long");

@ I'm trying to make the inner loop fast here, without really
knowing anything about the architecture on which this code is running.
Hopefully the pipeline won't stall except to the extent necessary, so that
the program is essentially able to operate at roughly the memory speed.

As a result if this logic, some classes might be discovered twice.
I don't really care, because I imagine the discoveries will be
few and far between.

@<Run through $5^r$ sequences, looking for cost savings@>=
for (j=n+1;j<n+r;j++) op[j]=4, x[j]=y[j]=x[jop[j]]^x[kop[j]],z[j]=mask>>1;
while (1) {
  register int d0,d1,d2,d3,d4;
  register truthtab aa,bb;
  aa=x[jop[n+r]], bb=x[n+r-1];
  d0=dist[aa&bb];
  d1=dist[aa&(~bb)];
  d2=dist[(~aa)&bb];
  d3=dist[aa|bb];
  d4=dist[aa^bb];
  @<Report success if any of |d0| thru |d4| are nonzero@>;
  @<Move to the next sequence of |op|s, but |break| if done@>;
}

@ @<Report success if any of |d0| thru |d4| are nonzero@>=
if (d0) {
  op[n+r]=0, x[n+r]=aa&bb;
  @<Report a success@>;
}
if (d1) {
  op[n+r]=1, x[n+r]=aa&(~bb);
  @<Report a success@>;
}
if (d2) {
  op[n+r]=2, x[n+r]=(~aa)&bb;
  @<Report a success@>;
}
if (d3) {
  op[n+r]=3, x[n+r]=aa|bb;
  @<Report a success@>;
}
if (d4) {
  op[n+r]=4, x[n+r]=aa^bb;
  @<Report a success@>;
}

@ @<Report a success@>=
c=classify(x[n+r]);
setcost(c);
count++, grandcount++;
fprintf(outfile,"%d: %08x via",grandcount,c->tt);
for (j=n+1;j<=n+r;j++)
  fprintf(outfile," %c=%c%c%c",
         regsym[j],regsym[jop[j]],opsym[op[j]],regsym[kop[j]]);
fprintf(outfile,"=%08x\n",x[n+r]);
fflush(outfile);

@ Here's an idea that should speed things up: There are $2^n$ ways
to complement subsets of the variables, and each of these ways transforms
one sequence of |op|s to another. We don't need to consider different
sequences that produce equivalent results; so we'll look only at opcode
sequences that are lexicographically smallest among all of their
complementations. For this purpose we maintain bit vectors |y[j]|
and |z[j]|, with 1-bits in |y[j]| where a complementation will
change~|x[j]| and with 1-bits in |z[j]| where a complementation
will not change |op[1]| through |op[j]|.

If |(y[kop[j]]&(~y[jop[j]])&z[j-1]| is nonzero, we needn't bother
with the case |op[j]=1|. The reason is that there's some way to
complement variables, preserving all opcodes below |op[j]| and
preserving |x[jop[j]]|, but complementing |x[kop[j]]|; thus
|op[j]=0| will satisfactorily cover this case. Furthermore, we
needn't bother with |op[j]=3| either, because complementing |x[kop[j]]|
will cover that case with |op[j]=2|.
With a similar argument we can often avoid opcode~2.

@<Move to the next sequence of |op|s, but |break| if done@>=
for (j=n+r-1;op[j]==0;j--) op[j]=4;
t=z[j-1];@+if (t) {
  if (j==n) break;
  @<Move carefully to the next sequence of |op|s@>;
} else@+{
  switch (--op[j]) {
case 0: x[j]=x[jop[j]]&x[kop[j]];@+ break;
case 1: x[j]=x[jop[j]]&(~x[kop[j]]);@+ break;
case 2: x[j]=(~x[jop[j]])&x[kop[j]];@+ break;
case 3: x[j]=x[jop[j]]|x[kop[j]];@+ break;
  }
  while (j<n+r-1) j++,x[j]=x[jop[j]]^x[kop[j]];
}

@ Complementation preserves an opcode if and only if the opcode is~4.

In this step I set |y[j]=0| whenever accepting an opcode less than~4.
Actually some complementation is propagated; for example, when
|op[j]=0|, the true value of |y[j]| is |y[jop[j]]&y[kop[k]]|, and when
|op[j]=3| the true value is $|y[jop[j]]|\mid|y[kop[k]]|$. But there's no
point in keeping 1-bits in |y[j]| where there are 0-bits in |z[j]|,
since the 1s won't change any essential behavior.

@<Move carefully to the next sequence of |op|s@>=
try_again: switch (--op[j]) {
case 0: x[j]=x[jop[j]]&x[kop[j]];
accept_it: y[j]=0, t=z[j]=z[j-1]&(~y[jop[j]])&(~y[kop[j]]);@+break;
case 1:@+if (t&(~y[jop[j]])&y[kop[j]]) goto try_again;
  x[j]=x[jop[j]]&(~x[kop[j]]);@+ goto accept_it;
case 2:@+if (t&y[jop[j]]&(~y[kop[j]])) goto try_again;
   x[j]=(~x[jop[j]])&x[kop[j]];@+ goto accept_it;
case 3:@+if (t&(y[jop[j]]|y[kop[j]])) goto try_again;
    x[j]=x[jop[j]]|x[kop[j]];@+ goto accept_it;
}
while (j<n+r-1) j++,x[j]=x[jop[j]]^x[kop[j]],y[j]=y[jop[j]]^y[kop[j]],z[j]=t;

@ @<Init...@>=
for (j=1;j<=n;j++)
  x[j]=y[j]=mask/((1<<(1<<(n-j)))+1), z[j]=mask>>1;
op[n]=1; /* a nonzero sentinel to stop the |op|-update loop */

@*Index.
