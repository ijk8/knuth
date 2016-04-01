\datethis
@*Intro. This simple program finds the canonical form of a Boolean
function $f(x_1,\ldots,x_n)$ under permutation and/or complementation
of variables, given its truth table on the command line (in hexadecimal
notation)..

For example, the ``two-out-of-five'' function $S_2(x_1,\ldots,x_5)$
has truthtable |0x16686880|. From the command line argument
\.{16686880}, this program returns ``\.{01161668(-5-3-1-2-4)}'';
the meaning is that, if $f(x_1,\ldots,x_5)$ and $g(x_1,\ldots,x_5)$
have the respective truth tables \.{16686880} and \.{01161668},
then we have
$f(x_1,x_2,x_3,x_4,x_5)=g(\bar x_5,\bar x_3,\bar x_1,\bar x_2,\bar x_4)$.
(There are of course 120 different ways to express the answer
in this particular case. The program lists the first that it happens to find.)

@d n 5 /* at most 5; if $<5$, must change the |sprintf| statement below */
@d nfactorial 120
@d nnn (nfactorial<<n)

@c
#include <stdio.h>
char delta[nnn]; /* for symmetries via exercise 7.2.1.2--20 */
typedef unsigned int truthtab;
truthtab ttarg; /* the truth table input on command line */
char perm[n+1]; /* the current signed permutation */
char ans[100];

main(int argc,char *argv[])
{
  register int i,j,k,d,s,comp;
  register truthtab t,tt;
  @<Initialize the |delta| table@>;
  if (argc!=2 || sscanf(argv[1],"%x",&ttarg)!=1) {
    fprintf(stderr,"Usage: %s truthtable-in-hex\n",argv[0]);
    exit(-1);
  }
  @<Set |ans| to the canonical code for truth table |ttarg|@>;
  printf("%08x is %s\n",ttarg,ans);
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

@ @d full_shift (1<<n)
@d half_shift (1<<(n-1))
@d quart_shift (1<<(n-2))
@d eighth_shift (1<<(n-3))
@d xvi_shift (1<<(n-4))
@d xxxii_shift (1<<(n-5))
@d mask ((unsigned int)((1<<full_shift)-1)) /* $2^{2^n}-1$ */
@d half_mask ((1<<half_shift)-1)
@d quart_mask ((1<<quart_shift)-1)
@d eighth_mask ((1<<eighth_shift)-1)
@d xvi_mask ((1<<xvi_shift)-1)
@d xxxii_mask ((1<<xxxii_shift)-1)
@d infty 999

@<Set |ans|...@>=
t=ttarg, tt=0xffffffff, comp=0;
for (j=1;j<=n;j++) perm[j]=j;
for (j=0;j<nnn;j++) {
  switch (delta[j]) {
    @<Cases to move to the next truth table@>@;
  }
  if (t<tt) {
    sprintf(ans,"%s%08x(%+d%+d%+d%+d%+d)",
      comp?"-":"",t,perm[1],perm[2],perm[3],perm[4],perm[5]);
    tt=t;
  }
}

@ @<Cases to move to the next truth table@>=
case 0: t=(t<<half_shift)+(t>>half_shift);
  if (n<5) t&=mask;
  perm[1]=-perm[1];
case -1:@+ if (t>(mask>>1)) t^=mask,comp^=1;
         /* complement so that $f(0,\ldots,0)=0$ */
  break;
case 1: d=(t^(t>>quart_shift))&(quart_mask<<quart_shift);
  t^=d+(d<<quart_shift);
  k=perm[1], perm[1]=perm[2], perm[2]=k;
  break;
case 2: d=(t^(t>>eighth_shift))&((eighth_mask<<eighth_shift)*(mask/half_mask));
  t^=d+(d<<eighth_shift);
  k=perm[2], perm[2]=perm[3], perm[3]=k;
  break;
case 3: d=(t^(t>>xvi_shift))&((xvi_mask<<xvi_shift)*(mask/quart_mask));
  t^=d+(d<<xvi_shift);
  k=perm[3], perm[3]=perm[4], perm[4]=k;
  break;
case 4: d=(t^(t>>xxxii_shift))&((xxxii_mask<<xxxii_shift)*(mask/eighth_mask));
  t^=d+(d<<xxxii_shift);
  k=perm[4], perm[4]=perm[5], perm[5]=k;
  break;

  
@*Index.
