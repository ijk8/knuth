\datethis
@*Intro. This program reads outputs of {\mc BDD11} into internal arrays,
by brute force.

With change files I can adapt it to other uses.

@d memsize 200000 /* this many nodes */
@d varsize 128 /* this many variables */
@d bdds 2 /* this many BDDs */
@d bufsize 100 /* buffer size; 100 is plenty big */

@c
#include <stdio.h>
#include <stdlib.h>
typedef struct {
  int v;
  int lo;
  int hi;
  int mark;
} node;
node* mem[bdds];
int root[bdds];
FILE *infile;
char buf[bufsize];
int i1,i2,i3,i4;
int memmax;
@<Subroutines@>@;

main(int argc,char *argv[]) {
  register int j,k,r,minv;
  for (r=0;r<bdds;r++) {
    mem[r]=(node*)malloc(memsize*sizeof(node));
    if (!mem[r]) {
      printf("Sorry, I can't allocate mem[%d]!\n",r);
      exit(-99);
    }    
    for (k=0;k<memsize;k++) mem[r][k].lo=mem[r][k].hi=0;
    if (!(infile=fopen(argv[r+1],"r"))) {
      printf("Sorry, I can't open `%s' for reading!\n",argv[r+1]);
      exit(-1);
    }
    for (k=0,minv=varsize;;) {
      if (!fgets(buf,bufsize,infile)) break;
      j=sscanf(buf,"%x: (~%d?%x:%x)\n",&i1,&i2,&i3,&i4);
      if (j!=4)
        printf("! I got only %d inputs from the line %s",j,buf);
      else {
        if (i1>memmax) memmax=i1;
        if (i3>memmax) memmax=i3;
        if (i4>memmax) memmax=i4;
        if (i1>=memsize || i2>=varsize || i3>=memsize || i4>=memsize) {
          printf("! address out of range in the line %s",buf);
          exit(-69);
        }@+else if (mem[r][i1].lo+mem[r][i1].hi)
          printf("! clobbered node in the line %s",buf);
        else {
          if (i2<minv) minv=i2,root[r]=i1;
          k++,mem[r][i1].v=i2, mem[r][i1].lo=i3, mem[r][i1].hi=i4;
        }
      }
    }
    printf("%d nodes input into mem%d\n",k,r);
    printf("(memmax=%d)\n",memmax);
  }
  @<Do our thing@>;
}

@ @<Sub...@>=

@ @<Do our thing@>=

@*Index.
 
