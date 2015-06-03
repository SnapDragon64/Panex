#include <stdio.h>

#define NIL 0
#define DEPTH 3
/* Search prohibits occupancy of top center position, which matters only
   for starting state */
/* printing won't work correctly for DEPTH > 16 */
/* search will fail above DEPTH > 84 */

#define NPIECES (2*DEPTH)
#define NPOSITIONS (3+3*DEPTH)
#define HASHSIZE  1299709 /* 15485863 1299709 611953 350377 47381 */
/* 67867967 was used to sove the DEPTH=8 problem on a 1GB machine, but
   any primes will do; larger reduces the linear search in a hash bucket */

/* a state is an assignment to an array of NPOSITIONS elements, where
   the pieces are coded (except that the internal representation is different):
   0: empty;
   2n + 1: black n;
   2n + 2: red n;
   The positions are coded:
   0   1   2
   3   4   5
   .    
   .    
   3*DEPTH ... 3*DEPTH+2
   
   Position 1 is never occupied (and no space is allocated for it).
*/

#define PBASE ((NPOSITIONS)/2)
/* The internal representation represents all positions except position 1 in a
   nybble.  The nybble contains the piece number, or 0, or 0xf.  0 means empty.
   0xff means the piece number is 15 or larger; the locations of these
   pieces is represented in the next PEXT bytes.  The positions are recoded
   so that the left and right columns are mixed in the high and low nybbles of
   the byte at index position/3, for indices 0 through DEPTH.
   The center column is stored in bytes DEPTH+1 through PBASE-1, low then
   high nybbles. */
#define PEXT ((NPIECES >= 15) ? (NPIECES - 14) : 0)
/* PEXT is even, so overflow pieces come in pairs, red and black.  The
   encoded positions are the address of the nybble, as defined above.
   If the piece has been removed from the puzzle, the position if 0xff. */
#define OWNER (PBASE + PEXT)
/* The OWNER byte is used to keep track of the state of the piece in the
   hash table, as defined below.  The hash table always stores only one
   of the four symmetrized positions [reflected, color-swapped, or both],
   the one with minimal lexicographic value.  Canonicalization of a state
   replaces a state and owner value with a minimalized value, and owner
   state producing the equivalent state (except for slight loss of information
   when multiple states are reachable) */

typedef struct STATE {
  unsigned char whosin[PBASE + PEXT + 1];
  /* use nybble 0xf to mean 0xf or larger;
     whosin[0..DEPTH] hold positions 02 35 68 ...
     whosin[DEPTH+1..PBASE] hold positions 47 10,13 ...
     store positions of pieces 0xf and larger in PEXT
  
     whosin[OWNER] is the sum of the following bits:
  */
#define B_OWNER 1 /* on if owner is 1, off if 0 */
#define B_ASIS 2 /* on if the state is in the table, reachable from B_OWNER */
#define B_SYM 4 /* on if the reflection + recoloring is in the table */
#define B_REFL 8 /* on if the reflection is in the table w/opposite owner */
#define B_RECL 16 /* on if the recoloring is in the table w/opposite owner */

  struct STATE *hashnext;
  struct STATE *next;
} STATE;


unsigned char getwhosin(STATE *state, int pos) {
  unsigned char res;
  if (pos >= NPOSITIONS)
    return 0xff;
  if (pos == 1)
    return 0;
  if ((pos % 3) == 1) {
    pos = pos / 3 + 2 * DEPTH + 1;
  } else {
    pos = (2 * pos) / 3;
  }
  
  res = state->whosin[pos/2];
  if (pos & 1) res >>= 4;
  res &= 0xf;
  if (res == 0xf) {
    int i;
    for (i = PBASE; i < PBASE + PEXT && state->whosin[i] != pos; i++)
      res++;
    if (i == PBASE + PEXT)
      exit(1);
  }
  return res;
}

void printastate(pstate) STATE *pstate; {
  static char *name[] = {"|","a","A","b","B","c","C","d","D","e","E",
			 "f","F","g","G","h","H","i","I","j","J",
			 "k","K","l","L","m","M","n","N","o","O","p","P"};
  int i,j;
  /*  printf("owner = %d\n", pstate->whosin[OWNER]); */
  for (i=0; i<=DEPTH; i++) {
    printf("                 ");
    for (j=0; j<3; j++)
      printf("%s  ",name[getwhosin(pstate,3*i+j)]);
    printf("\n");
  }
  /*
  printf("Owner = %x ", pstate->whosin[OWNER]);
  printf("Last empties:");
  for (i=0; i<3; i++)
    printf(" %d", getlastemptyincol(pstate, i));
  printf("\n");
  */
}

void listcount(pstate) STATE *pstate; {
	int i=0;
	while (pstate) {
		i++;
		pstate = pstate->next;
	}
	printf("%d",i);
}

void printalist(pstate) STATE *pstate; {
  while(pstate) {
    printastate(pstate);
    printf("\n");
    pstate = pstate->next;
  }
}

void setwhosin(STATE *state, int pos, unsigned char what) {
  unsigned char mask, nyb, whatwas;
  if (pos == 1)
    exit(1);
  if ((pos % 3) == 1) {
    pos = pos / 3 + 2 * DEPTH + 1;
  } else {
    pos = (2 * pos) / 3;
  }
  mask = (pos & 1) ? 0x0f: 0xf0;
  nyb = (what < 0xf) ? what * 17: 0xff;
  whatwas = state->whosin[pos/2];
  state->whosin[pos/2] = (nyb & ~mask) | (whatwas & mask);
  if (what >= 0xf) {
    state->whosin[PBASE+what-0xf] = pos;
  } else if (what == 0) {
    if (pos & 1)
      whatwas = whatwas >> 4;
    whatwas &= 0xf;
    if (whatwas == 0xf) {
      int i;
      for (i = PBASE; i < PBASE + PEXT && state->whosin[i] != pos; i++)
      if (i == PBASE + PEXT)
	exit(1);
      state->whosin[i] = 0xff;
    }
  }
}

unsigned char reflect_owner[32], recolor_owner[32];

/* Mirror image in to out */
static unsigned char refl[256];
void reflect(STATE *in, STATE *out) {
  int i;
  *out = *in;
  for (i = 0; i <= DEPTH; i++)
    out->whosin[i] = refl[in->whosin[i]];
  for (i = PBASE; i < PBASE + PEXT; i++)
    if (out->whosin[i] <= NPIECES)
      out->whosin[i] ^= 1;
  out->whosin[OWNER] = reflect_owner[in->whosin[OWNER]];
}

/* Color reverse in to out */
static unsigned char recl[256];
void recolor(STATE *in, STATE *out) {
  int i;
  *out = *in;
  for (i = 0; i< PBASE; i++)
    out->whosin[i] = recl[in->whosin[i]];
  while (i < PBASE + PEXT) {
    out->whosin[i+1] = in->whosin[i];
    out->whosin[i] = in->whosin[i+1];
    i += 2;
  }
  out->whosin[OWNER] = recolor_owner[in->whosin[OWNER]];
}

int owner(STATE *s) {
  int o = s->whosin[OWNER];
  if (o & (B_ASIS | B_SYM))
    return o & B_OWNER;
  return 1 ^ (o & B_OWNER);
}

void canonicalize(STATE *s) {
  STATE temp[4];
  int i;
  s->next = NIL;
  s->hashnext = NIL;
  temp[0] = *s;
  reflect(&temp[0], &temp[1]);
  recolor(&temp[0], &temp[2]);
  recolor(&temp[1], &temp[3]);
  /*
    printf("Canonicalizing: input=\n");
    printastate(&temp[0]);
    printf("Reflection=\n");
    printastate(&temp[1]);
    printf("Recoloring=\n");
    printastate(&temp[2]);
    printf("Symmetrizing=\n");
    printastate(&temp[3]);
  */
  i = compstate(&temp[0], &temp[3]);
  if (i == 0)
   temp[0].whosin[OWNER] |= temp[3].whosin[OWNER];
  else if (i > 0)
    temp[0] = temp[3];
  i = compstate(&temp[1], &temp[2]);
  if (i == 0)
    temp[1].whosin[OWNER] |= temp[2].whosin[OWNER];
  else if (i > 0)
    temp[1] = temp[2];
  i = compstate(&temp[0], &temp[1]);
  if (i == 0) {
    /* should never happen */
    printf("Curious state to canonicalize, equal to own reflection!");
    printastate(&temp[0]);
    exit(1);
    temp[0].whosin[OWNER] |= (temp[1].whosin[OWNER]) & ~B_OWNER;
  } else if (i > 0)
    temp[0] = temp[1];
  *s = temp[0];
  /*
    printf("Canonical choice:\n");
    printastate(s);
  */
}

void decanonicalize(STATE *s, unsigned char town) {
  /* pick a good reflection/recoloring of s and/or t which are eqstate */
  int i = 0;
  STATE temp;
  while (s->whosin[OWNER] && (i++ < 2)) {
    if (s->whosin[OWNER] & town & B_ASIS)
      return;
    if (s->whosin[OWNER] & town & B_REFL) {
      temp = *s;
      reflect(&temp, s);
      return;
    }
    recolor(s, &temp);
    town = recolor_owner[town];
    *s = temp;
  }
  printf("Ran out of mask in decanonicalize!");
  exit(1);
}

typedef struct treenode {
  STATE state;
  struct treenode *left,*right;
} treenode;

STATE *hashtable[HASHSIZE];

int compstate(STATE *s1, STATE *s2)
{
  register unsigned char *p1, *p2;
  register int i, diff;
  for(i=0, p1 = s1->whosin, p2 = s2->whosin; i<PBASE + PEXT; i++)
    if (diff = ((int)*p1++ - (int)*p2++)) return diff;
  return 0;
}

int eqstate(STATE *s1, STATE *s2)
{
  register unsigned char *p1, *p2;
  register int i;
  for(i=0, p1 = s1->whosin, p2 = s2->whosin; i<PBASE + PEXT; i++)
    if (*p1++ != *p2++) return 0;
  return 1;
}

treenode *tfreehead;

treenode *newtree() {
  int i;
  treenode *ans;
  if (!tfreehead) {
    tfreehead = (treenode *)(malloc((unsigned)128*sizeof(treenode)));
    for (ans = tfreehead, i=0; i<128; i++, ans++)
      ans->left = ans+1;
    (--ans)->left = NIL;
  }
  ans = tfreehead;
  tfreehead = tfreehead->left;
  return ans;
}

STATE *sfreehead;

int states_in_use, breadth;

STATE *newstate() {
  int i;
  STATE *ans;
  states_in_use++;
  if (!sfreehead) {
    sfreehead = (STATE *)(malloc((unsigned)128*sizeof(STATE)));
    for (ans = sfreehead, i=0; i<128; i++, ans++)
      ans->next = ans+1;
    (--ans)->next = NIL;
  }
  ans = sfreehead;
  sfreehead = sfreehead->next;
  return ans;
}

freestate(s)
     STATE *s;
{
  --states_in_use;
  if (s) {
    s->next = sfreehead;
    sfreehead = s;
  }
}

sfree(s)
     STATE *s;
{
  int i;
  STATE *temp;
  i=0;
  while (s) {
    i++;
    temp = s->next;
    freestate(s);
    s = temp;
  }
  if (i>breadth) breadth = i;
}

hash(pstate) STATE *pstate; {
  /* returns the hash function for the state */
  int i;
  unsigned h;
  h = 0;
  for (i=0; i < PBASE + PEXT; i++)
    h += pstate->whosin[i]<<i;
  h = h % HASHSIZE;
  return h;
}

inshash(STATE *pstate) {
  /* puts state into the hash table. */
  int h;
  STATE *temp;
  h = hash(pstate);
  pstate->hashnext = hashtable[h];
  hashtable[h] = pstate;
  /*
  for (temp=pstate->hashnext; temp; temp=temp->hashnext)
    if (temp == pstate)
      printf("*");
  */
}

void unhash(STATE *pstate) {
  /* delete the thing that pstate points to from the hash table. */
  int h;
  STATE *temp, *prev;
  h = hash(pstate);
  temp = hashtable[h];
  prev = NIL;
  while (temp) {
    if (eqstate(temp,pstate)){
      if (prev == NIL)
	hashtable[h] = temp->hashnext;
      else
	prev->hashnext = temp->hashnext;
      return;
    }
    prev = temp;
    temp = temp->hashnext;
  }
  printf("tried to unhash something not in the table\n");
  exit(0);
}

STATE *testhash(STATE *pstate) {
  int h /*, cnt = 0 */;
  STATE *temp;
  h = hash(pstate);
  temp = hashtable[h];
  while(temp) {
    if (eqstate(temp,pstate)) return temp;
    /*    if ((++cnt % 1000) == 0)
      printf("/");
    */
    temp = temp->hashnext;
  }
  return NIL;
} 

clearhash(STATE *list) {
  /* clear out the whole hash table */
  for ( ; list; list = list->next)
    hashtable[hash(list)] = NIL;
}

clearallhash() {
  int i;
  for (i=0; i<HASHSIZE; i++) hashtable[i] = NIL;
}

int getlastemptyincol(STATE *state, int col) {
  int mask, i;
  if (col == 1) {
    i = DEPTH + 1;
    while ((i < PBASE) && (state->whosin[i] == 0))
      i++;
    if (i == PBASE) {
      i = 3 * DEPTH + 1;
    } else if ((state->whosin[i] & 0xf) == 0) {
      i = 6 * (i - DEPTH) - 2;
    } else {
      i = 6 * (i - DEPTH) - 5;
    }
  } else {
    mask = (col == 0) ? 0xf : 0xf0;
    i = 0;
    while (i <= DEPTH && (state->whosin[i] & mask) == 0) {
      i++;
    }
    i = 3 * i + col - 3;
  }
  return i;
}

move(from,to,oldstate,newstate)
     STATE *oldstate,*newstate;
     /* return 0 if not a legal move */
{
  int who,where;
  
  if ((from == to) || (getwhosin(oldstate, to == 1 ? 4: to) != 0))
    return 0;
  where = getlastemptyincol(oldstate, from) + 3;
  if (where >= NPOSITIONS)
    return 0;
  *newstate = *oldstate;
  setwhosin(newstate, where, 0);
  who = getwhosin(oldstate, where);
  where = getlastemptyincol(newstate, to);
  if (((who + 1) / 2) < (where/3))
    where = ((who + 1)/2)*3 + to;
  setwhosin(newstate, where, who);
  return 1;
}

void dumpastate(state)
     STATE *state;
{
  static STATE laststate,tempstate;
  static neverhere = 1;
  static movenum = 0;
  int i,j;
  if (neverhere)
    neverhere = 0;
  else {
    for(i=0;i<3;i++)
      for(j=0;j<3;j++)
	if ((move(i,j,&laststate,&tempstate))
	    && (eqstate(&tempstate,state)))
	  goto printit;
  printit:
    printf("Move %d: %d->%d\n", ++movenum, i, j);
  }
  laststate = *state;
  printastate(state);
}
treenode *distfind(start,finish)
     STATE *start,*finish;
{
  treenode *answer;
  int i,j,cnt=0;
  STATE midpt;
  STATE *olist,*clist,*flist,*curstate,*temp, *hstart, *hfinish;
  /*
    printf("searching for midpoint between:\n");
    printastate(start);
    printf("and:\n");
    printastate(finish);
  */
  if (eqstate(start,finish)) {
    printf("equal states\n");
    return NIL;
  }
  hstart = newstate();
  *hstart = *start;
  hstart->whosin[OWNER] = B_ASIS;
  hfinish = newstate();
  *hfinish = *finish;
  hfinish->whosin[OWNER] = B_ASIS | B_OWNER;
  olist = flist = NIL;
  clist = hstart;
  canonicalize(hstart);
  canonicalize(hfinish);
  hstart->next = hfinish;
  hfinish->next = NIL;
  inshash(hstart);
  if (eqstate(hstart, hfinish)) {
    hstart->whosin[OWNER] |= hfinish->whosin[OWNER];
    hstart->next = NIL;
    freestate(hfinish);
  } else {
    inshash(hfinish);
  }
  /*
    printf("olist:\n");
    printalist(olist);
    printf("clist:\n");
    printalist(clist);
    printf("flist:\n");
    printalist(flist);
  */
  do  {
    /*
      printf("clist:\n");
      printalist(clist);
    */
    cnt += 2;
    printf(".");
    fflush(stdout);
    for (curstate = clist; curstate; curstate = curstate->next) {
      for(i=0;i<3;i++) for(j=0;j<3;j++) {
	if (move(i,j,curstate,&midpt)) {
	  canonicalize(&midpt);
	  temp = testhash(&midpt);
	  if (temp) {
	    if ((temp->whosin[OWNER] & 1) != (midpt.whosin[OWNER] & 1)) {
	      STATE *t;
	      for (t = flist; t && (t != temp); t = t->next)
		;
	      if (t == temp)
		cnt++;
	      /* printf("foundit!  Midpt =\n"); */
	      
	      decanonicalize(&midpt, temp->whosin[OWNER]);
	      /* printastate(&midpt); */
	      goto foundit;
	    } else {
	      temp->whosin[OWNER] |= midpt.whosin[OWNER];
	    }
	  } else {
	    temp = newstate();
	    *temp = midpt;
	    temp->next = flist;
	    flist = temp;
	    inshash(temp);
	  }
	}
      }
    }
/*
      printf("olist: ");
      listcount(olist);
      printf("; clist: ");
      listcount(clist);
      printf("; flist: ");
      listcount(flist);
printf("\n");
*/
    for (curstate = olist; curstate; curstate = curstate->next)
      unhash(curstate);
    sfree(olist);
    olist = clist;
    clist = flist;
    flist = NIL;
  }  while (clist);
  printf("Start and finish are not connected!\n");
  exit(0);
 foundit:
  clearhash(olist);
  clearhash(clist);
  clearhash(flist);
  sfree(olist);
  sfree(clist);
  sfree(flist);
  printf("%d\n,", cnt-1);
  if (cnt == 77)
    printf("Yikes\n");
  if (eqstate(start,&midpt) || eqstate(&midpt,finish))
    return NIL;
  answer = newtree();
  answer->state = midpt;
  answer->left = distfind(start,&midpt);
  answer->right = distfind(&midpt,finish);
  return answer;
}

void showpath(node)
     treenode *node;
{
  if (!node)
    return;
  showpath(node->left);
  dumpastate(&(node->state));
  showpath(node->right);
}

main() {
  static STATE start, finish;
  treenode *root;
  int i,j;
  for (i = 0; i < 0x10; i++)
    for (j = 0; j < 0x10; j++)
      refl[(i<<4) + j] = (j<<4) + i;
  recl[0] = 0;
  recl[0xf] = 0xf;
  for (i = 1; i < 0xf; i++)
    recl[i] = ((i+1) ^ 1) - 1;
  for (i = 0; i < 0x10; i++) {
    for (j = 1; j < 0x10; j++)
      recl[(j<<4) + i] = (recl[j] << 4) + recl[i];
  }
  for (i = 0; i < 32; i++) {
    int valrefl = 0;
    int valrecl = 0;
    if (!(i & B_OWNER)) {
      valrefl |= B_OWNER;
      valrecl |= B_OWNER;
    }
    if (i & B_ASIS) {
      valrefl |= B_REFL;
      valrecl |= B_RECL;
    }
    if (i & B_SYM) {
      valrefl |= B_RECL;
      valrecl |= B_REFL;
    }
    if (i & B_REFL) {
      valrefl |= B_ASIS;
      valrecl |= B_SYM;
    }
    if (i & B_RECL) {
      valrefl |= B_SYM;
      valrecl |= B_ASIS;
    }
    reflect_owner[i] = valrefl;
    recolor_owner[i] = valrecl;
  }
  for (i = 0; i < PBASE + PEXT; i++)
    start.whosin[i] = finish.whosin[i] = 0;
  for (i = 0; i < DEPTH; i++) {
    setwhosin(&start, 3*i+3, 2*i + 1);
    setwhosin(&start, 3*i+5, 2*i + 2);
    setwhosin(&finish, 3*i+5, 2*i + 1);
    setwhosin(&finish, 3*i+3, 2*i + 2);
  }
  root = distfind(&start,&finish);
  printf("\n");
  dumpastate(&start);
  showpath(root);
  dumpastate(&finish);
  printf("breadth = %d; states in use = %d\n", breadth, states_in_use);
}
