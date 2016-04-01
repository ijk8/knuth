\datethis
@*Intro. This program (a development of the {\mc CHAINS} program that I wrote
a month or so ago) generates all $r$-step ``chains'' for functions
of $n$ variables, namely all sequences $(a_1,\ldots,a_{n+r})$ with the
property that $a_i=x_i$ for $1\le i\le n$ and $a_i=a_{j_i}\circ a_{k_i}$
for $n<i\le n+r$, where $1\le j_i<k_i<i$. Furthermore each of
$a_1$,~\dots,~$a_{n+r-1}$ is supposed to occur at least once on the
right-hand side. The latter condition implies that $r\ge n-1$.

And furthermore, this program produces only ``special'' chains,
which are relevant to nonobvious tricks of computation. A special
chain has three properties: (1)~It is not ``flawed,'' in the
sense that uses two or more steps to compute what could
be done in one step. (Flawed solutions are flagged by the {\mc CHAINS}
program; every flawed solution can be converted into a flawless one.)
(2)~It is not a simple extension of a chain with $n-1$ variables
and $r-1$ steps. Equivalently, if $j_i\le n$ and $k_i\le n$, then
both $j_i$ and $k_i$ must occur elsewhere in the chain.
(3)~The left and right subtrees of the root have at least one common node.

A chain defines a directed acyclic graph in which the nodes have
respective in-degrees $(u_1,\ldots,u_{n+r})$ and out-degrees
$(v_1,\ldots,v_{n+r})$, where $u_1=\cdots=u_n=0$, $u_{n+1}=\cdots=u_{n+r}=2$,
$v_{n+r}=0$, and $v_1$,~\dots,~$v_{n+r-1}>0$. Two chains are considered
equivalent if the associated dags are isomorphic; this program produces
exactly one representative of each equivalence class.

The canonical representation is found as follows: Each dag can be linearized
by topological sorting the operation nodes $(n+1,\ldots,n+r)$ in all possible
ways, and the variable nodes $(1,\ldots,n)$ can be permuted in $n!$ ways.
Every combination of topological sorting and permutation corresponds to
a chain, and the lexicographically smallest of all these chains is output.

Consequently we can always assume that $a_{n+1}=a_1\circ a_2$. Furthermore,
if $k_{i+1}<i$ we must have $(j_i,k_i)\le (j_{i+1},k_{i+1})$, since steps
$a_i$ and $a_{i+1}$ can be interchanged. (The case of equality is
explicitly allowed. For example, one of the important chains for
$n=4$ and $r=5$ is
$$
a_1=x_1,\enspace
a_2=x_2,\enspace
a_3=x_3,\enspace
a_4=x_4,\enspace
a_5=a_1\circ a_2,\enspace
a_6=a_1\circ a_2,\enspace
a_7=a_3\circ a_5,\enspace
a_8=a_4\circ a_6,\enspace
a_9=a_7\circ a_8.
$$
Each `$\circ$' actually stands for a {\it generic\/} operator; thus
the stated chain serves as a template for Boolean chains that
compute $a_5=a_1\land a_2$ and $a_6=a_1\lor a_2$.)

In order to avoid subtle errors, I'm pretty much using brute force here.

@d n 5 /* this many variables */
@d r 10 /* this many operations; should exceed $n$ */
@d nfactorial 120
@c
#include <stdio.h>
int j[n+r+1], k[n+r+1]; /* the indices $j_i$ and $k_i$ */
int needed[n+r+1][n+r]; /* indices that haven't yet appeared on the right */
int size[n+r+1]; /* the number of such indices at each level */
int ptab[nfactorial]; /* indices for permutations */
int perm[n+r+1]; /* the current permutation */
char prec[r+1][r+1]; /* precedence relation for topological sort */
char tops[r+1], itops[r+1]; /* topological sort and its inverse */
char deg[n+r+1]; /* out-degrees of nodes */
int nodes[n+r]; /* used to decide disjointness */
char ddeg[n+1],mate[n+1],dmate[n+1]; /* used to decide tameness */
int count,bigcount,badcount;
char code[]="0123456789abcdefghijklmnopqrstuvwxyz";

main()
{
  register int d,i,p,q,s;
  @<Initialize the tables@>;
  @<Backtrack through all solutions@>;
  printf("Altogether %d solutions (culled from %d), %d tame.\n",
                count,bigcount,badcount);
}

@ One subtle point arises here: Criterion (2) of specialness is {\it not\/}
the same as saying that ``every variable occurs at least once in a step
with a non-variable.'' The latter condition is sufficient, but not
necessary; for example, the chain
$$a_4=a_1\circ a_2,\quad
  a_5=a_1\circ a_3,\quad
  a_6=a_2\circ a_3,\quad
  a_7=a_4\circ a_5,\quad
  a_8=a_6\circ a_7$$
with $n=4$ fails to have that property, but it is clearly special.

The only other thing that requires ``thought'' is
the observation that the |size| can decrease by at most 1 at each
step; hence we can backtrack early if |size| gets too large.

If |size| is at or near its critical value, we must use one or
two of the |needed| values. But, as I said, this program is not
optimized for speed, so it spins its wheels instead of
exploiting such a fact.

@<Backtrack through all solutions@>=
  i=n+1, j[i]=1, k[i]=2;
  for (p=1,q=0;p<=n+1;p++,q++) needed[i][q]=p;
moveup: deg[j[i]]++, deg[k[i]]++, size[i++]=q;
  if (i>n+r) {
    @<If the left and right subtrees are disjoint, |goto backup|@>;
    @<Run through all topological sorts and permutations;
          |goto done| if a smaller solution is found@>;
    count++;@+@<Output the solution@>;
 done: bigcount++;
    goto backup;
  }
  j[i]=1, k[i]=2;
tryit:@+ if (k[i]<i-1) {
    if (j[i-1]>j[i]) goto again;
    if (j[i-1]==j[i] && k[i-1]>k[i]) goto again;
  }
  @<If step |i| is flawed, |goto again|@>;
  for (p=q=0;p<size[i-1];p++) {
    if (needed[i-1][p]==j[i] && 
          (k[i]>n || deg[j[i]])) continue; /* no longer needed */
    if (needed[i-1][p]==k[i] &&
          (k[i]>n || deg[k[i]])) continue; /* no longer needed */
    needed[i][q++]=needed[i-1][p]; /* still needed */
  }
  needed[i][q++]=i;
  if (q<=(1+n+r)-i) goto moveup; /* think */
again:@+if (k[i]<i-1) {
    k[i]++;@+goto tryit;
  }
  j[i]++, k[i]=j[i]+1;
  if (k[i]<i) goto tryit;
backup: i--;
  deg[j[i]]--, deg[k[i]]--;
  if (i>n+1) goto again;
  @<Make sure that all degrees are now zero@>;

@ A ``flawed'' solution has one or more computational steps
where $a_i$ depends on only two things but it involves
more than one step of computation. For example, a chain
with $a_{n+1}=a_1\circ a_2$ and $a_{n+2}=a_1\circ a_{n+1}$ is flawed.
So is a chain with, say,
$a_i=a_{i-2}\circ a_{i-1}$ and $a_{i+1}=a_{i-2}\circ a_i$,
even when $i>n+1$.

@<If step |i| is flawed, |goto again|@>=
if (k[i]>n) {
  if ((j[i]==j[k[i]] || j[i]==k[k[i]]) ||
         (j[i]>n && j[j[i]]==j[k[i]] && k[j[i]]==k[k[i]])) 
    goto again;
}

@ @<If the left and right subtrees are disjoint, |goto backup|@>=
for (q=n+1;q<n+r-1;q++) if (deg[q]>1) goto maybe;
goto backup;
maybe:@+ for (q=n+1;q<n+r;q++)
  nodes[q] = (1<<(q-n-1)) | nodes[j[q]] | nodes[k[q]];
if ((nodes[j[q]]&nodes[k[q]])==0) goto backup;

@ Algorithm 7.2.1.2V is used here. But the quantities called
$(n,a,a',j,k,l)$ in that algorithm are now called $(r,|tops|,|itops|,p,q,s)$.

@<Run through all top...@>=
@<Set up the |prec| table of topological constraints@>;
v1:@+ for (p=1;p<=r;p++) tops[p]=itops[p]=p;
v2:@+ @<Run through all permutations;
          |goto done| if a smaller solution is found@>;
   q=r;
v3:@+ p=itops[q], s=tops[p-1];
   if (prec[s][q]) goto v5;
v4:@+ tops[p-1]=q, tops[p]=s, itops[q]=p-1, itops[s]=p;
   goto v2;
v5:@+ while (p<q) s=tops[p+1], tops[p]=s, itops[s]=p, p++;
   tops[q]=itops[q]=q;
   q--;
   if (q) goto v3;

@ @<Set up the |prec| table...@>=
for (p=1;p<=r;p++) {
  for (q=1;q<=r;q++) prec[q][p]=0;
  if (j[n+p]>n) prec[j[n+p]-n][p]=1;
  if (k[n+p]>n) prec[k[n+p]-n][p]=1;
}

@ @<Init...@>=
for (p=1;p<=r;p++) prec[0][p]=1;

@ I'm using Algorithm 7.2.1.2T for permutations. The quantities
called $(N,t,m,j,k)$ in the book are $(s,|ptab|,i,p,q)$ here.

@ @<Init...@>=
t1:@+ s=nfactorial, d=s>>1, ptab[d]=1, i=2;
t2:@+ if (i==n) goto t6;
  i++, d=d/i, q=0;
t3:@+ for (q+=d, p=i-1; p; p--,q+=d) ptab[q]=p;
t4:@+ ptab[q]++, q+=d;
t5:@+ while (p<i-1) p++,ptab[q]=p,q+=d;
  if (q<s) goto t3;
  goto t2;
t6:@;

@ @<Run through all perm...@>=
for (q=1;q<=n;q++) perm[q]=q;
for (q=1;q<=r;q++) perm[n+q]=n+itops[q];
for (p=1;;p++) {
  for (q=1;q<=r;q++) {
    register int a=perm[j[n+tops[q]]], b=perm[k[n+tops[q]]];
    if (a<b) {
      if (a<j[n+q]) goto done;
      if (a>j[n+q]) goto nextp;
      if (b<k[n+q]) goto done;
      if (b>k[n+q]) goto nextp;
    }@+else@+{
      if (b<j[n+q]) goto done;
      if (b>j[n+q]) goto nextp;
      if (a<k[n+q]) goto done;
      if (a>k[n+q]) goto nextp;
    }
  }
nextp: if (p==nfactorial) break;
  q=ptab[p], s=perm[q+1], perm[q+1]=perm[q], perm[q]=s;
}

@ To check the validity of our work, we can verify that
the degree calculations haven't gone awry.

@<Make sure that all degrees are now zero@>=
for (q=1;q<=n+r;q++) if (deg[q])
  printf("Oops ... this can't happen (deg[%d]=%d)!\n",q,deg[q]);

@ We simply output digit-pairs $j_{n+q}k_{n+q}$ for $1\le q\le r$.

@<Output...@>=
printf("%d:",count);
for (q=1;q<=r;q++) printf(" %c%c",code[j[n+q]],code[k[n+q]]);
@<Print an asterisk if this solution is tame@>;
printf("\n");

@ A ``tame'' chain contains steps $a_i=x_j\circ x_k$
and $a_{i'}=x_j\circ x_k$ such that $x_j$ and $x_k$ occur nowhere else.

Any tame chain must
begin $a_{n+1}=a_1\circ a_2$ and $a_{n+2}=a_1\circ a_2$, because
of our canonical form. But those first two steps need not
actually be the tame ones.

@<Print an asterisk...@>=
if (k[n+2]==2) {
  for (q=1;q<=n;q++) ddeg[q]=dmate[q]=0;
  for (q=1;q<=r;q++) {
    if (k[n+q]<=n)
      ddeg[k[n+q]]++,mate[k[n+q]]=j[n+q],dmate[k[n+q]]^=j[n+q];
  }
  for (q=2;q<=n;q++)
    if (deg[q]==2 && ddeg[q]==2 && deg[mate[q]]==2 && dmate[q]==0) {
      printf(" *");
      badcount++;
      break;
    }
}

@*Index.
