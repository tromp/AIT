// John Tromp's Binary Lambda Calculus universal machine based on Ben Lynn's
// ION machine at https://crypto.stanford.edu/~blynn/compiler/ION.html

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <getopt.h>
#include <assert.h>
#include <time.h>

enum {
  STACKRAIL = 2, // mimimum distance from top of stack to end of stack due to 'I' rewrite
  NCOMB = 128, // memory addresses 0..NCOMB-1 represent primitive combinators like 'S' or 'K' by ASCII code
  FILEPATHLEN = 256, // maximum length of filepaths for blc programs in composition
  MINMEMSZ = 1<<20, // starting memory size
  MAXMEMSZ = 1<<31, // memory won't be doubled beyond this size
  STEPMASK = (1<<28)-1 // how often to report on reducting steps
};

typedef uint32_t u32;
u32 memsize, // current size of both mem and gcmem heaps in units of u32
    *mem,    // main memory heap holding LC and CL terms and on which graph reduction happens
    *gcmem,  // 2nd heap where GC stores all accessible terms before swapping back with main
    *spTop,  // top of stack which is at top of memory (mem + memsize - STACKRAIL)
    *sp,     // stack pointer; stack grows down from top holding spine of CL applications
    hp,      // heap pointer where new app nodes are allocated
    qOpt,    // flag for whether to perform some rare/impossible combinator rewrites in parsing
    qBLC2,   // flag for parsing BLC2 in which de Bruijn indices are Levenshtein encoded
    dbgGC,   // flag for providing stats on all Garbage Collection operations
    dbgSTP;  // flag for regularly reporting on number of graph reduction steps

// Hello. My name is Inigo Montoya. You killed my father. Prepare to
void die(char *s) {
  fprintf(stderr, "error: %s\n", s);
  exit(1);
}

static inline u32 isComb(u32 n) {
  return n < NCOMB;
}

// create application of f to x at end of heap
static inline u32 app(u32 f, u32 x) {
  mem[hp] = f;
  mem[hp+1] = x;
  return (hp += 2) - 2;
}

FILE *fp;
u32 nbits, inbits, mode;

// read 1 bit from file pointer fp, using inbits as a 1-byte buffer
// mode=0 for 1 bit per byte; mode=7 for 8 bits per byte
u32 getbit() {
  if (!nbits) {
    nbits = mode;
    inbits = getc(fp);
  } else nbits--;
  return (inbits>>nbits) & 1;
}

// create the equivalent of f applied to a
u32 clapp(u32 f, u32 a) {
  return // these rewrites are known to help. BTW, switch(f) and switch(mem[f]) turn out to be WAY slower
         f=='K' && a=='I' ? 'F'				// K I x y = I y = y = F x y
       : f=='B' && a=='K' ? 'D'				// B K x y z = K (x y) z = x y = D x y z
       : f=='C' && a=='I' ? 'T'				// C I x y = I y x = y x = T x y
       : f=='D' && a=='I' ? 'K'				// D I x y = I x = x = K x y
       : mem[f]=='B' && a=='I'? mem[f+1]		// B M I x = M (I x) = M x
       : mem[f]=='R' && a=='I'? app('T',mem[f+1])	// R M I x = I x M = x M = T M x
       : mem[f]=='B' && mem[f+1]=='C' && a=='T'? ':'	// B C T x y z = C (T x) y z = T x z y = z x y
       : mem[f]=='S' && mem[f+1]=='I' && a=='I'? 'M'	// S I I x = I x (I x) = x x = M x
       : !qOpt ? app(f, a)
         // ones below require -q but never seem to occur
       : f=='F' ? 'I'					// F I x = x = I x
       : f=='S' && a=='K' ? 'F'				// S K x y = K y (x y) = y = F x y
       : f=='B' && a=='I' ? 'I'				// B I x y = I (x y) = I x y
       : f=='C' && a=='C' ? 'R'				// C C x y z = C y x z = y z x = R x y z
       : mem[f]=='B' && mem[f+1]=='S' &&  a=='K'? 'B'	// B S K x y z = S (K x) y z = K x z (y z) = x (y z)
       : mem[f]=='B' && mem[mem[f+1]]=='S' && a=='K'	// B (S M) K x y = S M (K x) y = M y (K x y) = M y x
                          ? app('C',mem[mem[f+1]+1])	// = C M x y
       : mem[a]=='K' && f=='S'? app('B',mem[a+1])	// S (K M) x y = K M y (x y) = M (x y) = B M x y
       : mem[f]=='R' && mem[f+1]=='I' && a=='B'? 'I'	// R I B x y = B x I y = x (I y) = x y
         // no optimization possible, so just make a new app node
       : app(f, a);
}

// parse blc encoded lambda term from file pointer fp,
// (ab)using pseudo combinators V and L to represent variables and lambdas
u32 parseBLC() {
  u32 x;
  if (getbit()) {
    for (x=0; getbit(); x++) { }
    return app('V', x);
  }
  u32 isApp = getbit();
  x = parseBLC();
  return isApp ? app(x, parseBLC()) : app('L', x);
}

// parse Levenshtein encoded natural number where
// code(0) = 0
// code(n+1) = 1 code(l(n)) n
// e.g. code(5) = code(4+1) = 1 1100 01
//      code(2) = code(1+1) = 1 10 0
//      code(1) = code(0+1) = 1 0
u32 levenshtein() {
  if (!getbit()) return 0;
  u32 x, l = levenshtein();
  for (x=1; l--; ) x = 2*x + getbit();
  return x;
}

// parse blc encoded lambda term from file pointer fp,
// (ab)using pseudo-combinators V and L to represent variables and lambdas
u32 parseBLC2() {
  u32 x;
  if (getbit()) {
    return app('V', levenshtein());
  }
  u32 isApp = getbit();
  x = parseBLC2();
  return isApp ? app(x, parseBLC2()) : app('L', x);
}

// if DB term has all occurances of Var n doubled, return undoubled version, else return 0
u32 unDoubleVar(u32 n, u32 db) {
  u32 udf, f = mem[db];
  if (f == 'V') {
    assert(mem[db+1] != n); // should be guaranteed by parent calls
    return db;
  }
  u32 uda, a = mem[db+1];
  if (f == 'L')
    return (uda = unDoubleVar(n+1,a)) ? app('L', uda) : 0;
  u32 qf = mem[f]=='V' && mem[f+1]==n;
  u32 qa = mem[a]=='V' && mem[a+1]==n;
  if (qf && qa) return app('V',n);
  if (qf || qa) return 0;
  return (udf = unDoubleVar(n,f)) && (uda = unDoubleVar(n,a)) ? app(udf,uda) : 0;
}

// recognize recursive functions by (\x.x x) (\x. f (x x)) template
// note that \x. x x would have been converted to clapp(clapp('S','I'),'I') = 'M'
u32 recursive(u32 f, u32 a) {
  return f=='M' && mem[a]=='L' && mem[f=mem[a+1]]!='V' && (f=unDoubleVar(0,f)) ? app('L',f) : 0;
}

// combine step of Kiselyov bracket abstraction, explained in
// https://crypto.stanford.edu/~blynn/lambda/kiselyov.html
// based on the paper https://okmij.org/ftp/tagless-final/ski.pdf
// we store list of booleans bools as foldr (\bool n-> app(n,bool?1:0)) 0 bools
u32 combineK(u32 n1, u32 d1, u32 n2, u32 d2) {
  if (n1==0)
    return n2==0 ? clapp(d1,d2)
     : mem[n2+1] ? combineK(0,clapp('B',d1), mem[n2],d2)
     :             combineK(0,          d1 , mem[n2],d2);
  else if (mem[n1+1])
    return n2==0 ? combineK(0,clapp('R',d2), mem[n1],d1)
     : mem[n2+1] ? combineK(mem[n1],combineK(0,'S', mem[n1],d1), mem[n2],d2)
     :             combineK(mem[n1],combineK(0,'C', mem[n1],d1), mem[n2],d2);
  else
    return n2==0 ? combineK(mem[n1],d1, 0,d2)
     : mem[n2+1] ? (!mem[n2] && mem[n2+1] && d2=='I' ? d1 // eta optimization not handled by clapp
                 : combineK(mem[n1],combineK(0,'B', mem[n1],d1), mem[n2],d2))
         :         combineK(mem[n1],d1, mem[n2],d2);
}

// zipWith(bitwise or) two list of booleans
u32 zip(u32 nf, u32 na) {
  return !nf ? na : !na ? nf : app(zip(mem[nf],mem[na]),mem[nf+1] | mem[na+1]);
}

// convert lambda calculus to combinatory logic by Kiselyov's algorithm
// set list pn of booleans indicating variable use
u32 convertK(u32 db, u32 *pn) {
  u32 nf, cf, na, ca, f = mem[db], a = mem[db+1];
  if (f == 'V') {
    for (nf = app(0,1); a--; ) nf = app(nf,0);
    *pn = nf;
    return 'I';
  }
  if (f == 'L') {
    ca = convertK(a, &na);
    if (na==0) { *pn = 0; return clapp('K', ca); }
    else { *pn = mem[na]; return mem[na+1] ? ca : combineK(0,'K', *pn,ca); }
  }
  cf = convertK(f, &nf);
  if (!nf && (ca = recursive(cf,a))) { cf = 'Y'; a = ca; }
  ca = convertK(a, &na);
  *pn = zip(nf, na);
  return combineK(nf,cf, na,ca);
}

// call Kiselyov bracket abstraction and verify lack of free variables
u32 toCLK(u32 db) {
  u32 n, cl = convertK(db,&n);
  if (n) die("program not a closed term");
  return cl;
}

// evacuate cell n from mem to gcmem returning new index
u32 evac(u32 n) {
  if (isComb(n))
    return n;	// only applications need to migrate
  assert((n&1) == 0);
  u32 x = mem[n];
  u32 y = mem[x];
  while (y == 'T') {		// migrate T M N as N M
    mem[n] = y = mem[n+1];	// N
    mem[n+1] = mem[x+1];	// M
    y = mem[x = y];
  }
  if (y == 'K') {		// migrate K M N as I M
    mem[n+1] = mem[x+1];	// M
    x = mem[n] = 'I';
  } else if (y == 'F') {	// migrate F M N as I N
    x = mem[n] = 'I';
  }
  y = mem[n + 1];
  if (!x) return y;		// !x signals past migration to y
  if (x == 'I') {
    mem[n] = 0;
    return mem[n+1] = evac(y);
  }
  u32 hp0 = hp;
  gcmem[hp++] = x; gcmem[hp++] = y;	// migrate x y
  mem[n] = 0;				// signal migration to
  mem[n+1] = hp0;			// new index
  return hp0;
}

// reallocate m to fit size u32's, zeroing the NCOMB primitive combinators
u32 *reheap(u32* m, u32 size) {
  m = realloc(m, (size_t)size * sizeof(u32));
  if (!m)
    die("realloc failed");
  memset(m, 0, NCOMB * sizeof(u32)); // allow mem[x]=='C' test without !isComb(x)
  return m;
}

u32 steps, nGC, qDblMem;
void putch(u32 c) {
  putchar(c);
  fflush(stdout);
}

void stats() {
  fprintf(stderr, "\nsteps %u heap %u stack %td\n", steps, hp, spTop - sp);
}

// run garbage collector
void gc() {
  nGC++;
  if (dbgGC) {
    stats();
    fprintf(stderr, "memsize %u GC %u -> ", memsize, hp-NCOMB);
  }
  if (qDblMem)
    gcmem = reheap(gcmem, memsize *= 2);
  sp = gcmem + memsize - STACKRAIL;
  u32 di = hp = NCOMB;
  // gcmem[NCOMB..di-1] already index gcmem
  // gcmem[di..hp-1] still index old mem
  for (*sp = evac(*spTop); di < hp; di++)
    gcmem[di] = evac(gcmem[di]);
  if (dbgGC)
    fprintf(stderr, "%u\n", hp-NCOMB);
  spTop = sp;
  u32 *old = mem;
  mem = gcmem;
  gcmem = old;
  if (qDblMem)
    gcmem = reheap(gcmem, memsize);
  qDblMem = hp >= memsize/2 && memsize < MAXMEMSZ;
}

static inline u32 arg(u32 n) {
  return mem[sp[n] + 1];
}

static inline u32 apparg(u32 i, u32 j) {
  return app(arg(i), arg(j));
}

static inline void lazy(u32 delta, u32 f, u32 x) {
  sp += delta;
  assert(sp < spTop);
  u32 *p = mem + sp[1];
  p[0] = f; p[1] = x;
}

static inline void lazY(u32 delta, u32 f) {
  sp += delta;
  if (sp >= spTop)
    return;
  assert(sp < spTop);
  mem[sp[1]] = f;
}

void run(u32 x) {
  *(sp = spTop = mem + memsize - STACKRAIL) = x;
  for (char outbits = 0; ; steps++) {
    if (dbgSTP && !(steps & STEPMASK))
      stats();
    if (mem + hp > sp - 48) { // allow up to 40/2 apps after 8 sp--
      gc();
      x = *sp;
    }
    if (!isComb(x) && !isComb(x = mem[*sp-- = x]) && !isComb(x = mem[*sp-- = x])
                   && !isComb(x = mem[*sp-- = x]) && !isComb(x = mem[*sp-- = x])
                   && !isComb(x = mem[*sp-- = x]) && !isComb(x = mem[*sp-- = x])
                   && !isComb(x = mem[*sp-- = x]) && !isComb(x = mem[*sp-- = x])
       ) continue;
    switch (x) {
      case 'M': lazY(0, x = arg(1)); break;
      case 'Y': lazy(0, x = arg(1), app('Y',arg(1))); break;
      case '+': lazy(0, x = app(arg(1),'0'), '1'); break; // output bits
      case '>': lazy(0, x = app(arg(1),'+'), '!'); break; // output bytes
      case 'I': lazY(1, x = arg(1)); break;
      case 'F': lazY(1, x = 'I'); break;
      case 'K': lazy(1, x = 'I', arg(1)); break;
      case 'T': lazy(1, x = arg(2), arg(1)); break;
      case 'D': lazy(2, x = arg(1), arg(2)); break;
      case 'B': lazy(2, x = arg(1), apparg(2,3)); break;
      case 'C': lazy(2, x = apparg(1,3), arg(2)); break;
      case 'R': lazy(2, x = apparg(2,3), arg(1)); break;
      case ':': lazy(2, x = apparg(3,1), arg(2)); break;
      case 'S': lazy(2, x = apparg(1,3), apparg(2,3)); break;
      case '0':
      case '1': if (mode)
                  outbits = outbits<<1 | (x&1);             // output bit
                else putch(x);
                lazy(0, x = arg(1), '+'); break;
      case '!': putch(outbits);                           // output byte
                lazy(0, x = arg(1), '>'); break;
      case '-': getbit(); nbits++;                        // input
                if (inbits == EOF) {
                  if (fp == stdin) lazy(0, x = 'K', 'I');
                  else { fp = stdin; nbits = 0; }         // allow reading from program file
                  break;
                }
                if (mode) {
                  for (x='F'; nbits; nbits--,inbits>>=1)
                    x = app(app(':', "KF"[inbits&1]), x);
                } else x = "KF"[getbit()];
                lazy(0, x = app(':', x), app('-','?')); break;
      case 'V': return;                                   // end-of-output / variable
      default: die("unknown combinator");
    }
  }
}

void show(u32 n) {
  if (!isComb(n)) {
    u32 f = mem[n], a = mem[n+1];
    if (f == 'V') putch('0'+a);
    else if (f == 'L') { putch('\\'); show(a); }
    else { putch('`'); show(f); show(a); }
  } else putch(n);
}

void showNL(u32 n) {
  show(n);
  putchar('\n');
}

// Instead of running   (cat prog.blc8 -) | ./uni
// or                   (cat prog.blc  -) | ./uni -b
// one can now run these as                 ./uni [-b] prog

// Any input that prog has embedded in its file after its lambda term
// will be effectively preprended to stdin

// It's also possible to run multiple programs in sequence,
// provided they have no embedded input (uni will error if they do):
// uni [options] prog1 prog2 prog3 is equivalent to ./uni [options] prog123
// where prog123 is the function composition prog3 . prog2 . prog1

// Each prog$i is parsed from file $BLCPATH/prog$i.blc$suff
// where suffix $suff is a substring of "28" depending on the options.
// Digit '2' denotes Levenshtein coding, and digit '8' denotes byte mode.
//
// For example, the separate steps of section "Converting between bits and bytes"
// in https://www.ioccc.org/2012/tromp/hint.html can be replaced by 
/* echo "\a a ((\b b b) (\b \c \d \e d (b b) (\f f c e))) (\b \c c)" | uni parse deflate > rev.blc8
HELP */
// since neither parse nor deflate has embedded input.

int main(int argc, char **argv) {
  u32 db, dbgProg;
  dbgGC = dbgProg = dbgSTP = qBLC2 = qOpt = qDblMem = nbits = db = steps = nGC = 0;
  memsize = MINMEMSZ;
  mode = 7;                         // default byte mode
  int opt;
  while ((opt = getopt(argc, argv, "bghlpqsx")) != -1) {
    switch (opt) {
      case 'b': mode = 0; break;    // bit mode
      case 'l': qBLC2 = 1; break;   // parse BLC2 aka Levenshtein coding
      case 'g': dbgGC = 1; break;   // show garbage collection stats
      case 'h': printf("usage: grep -C 19 ^HELP uni.c\n"); exit(0);
      case 'p': dbgProg = 1; break; // print parsed program
      case 'q': qOpt = 1; break;    // questionable clapp optimizations
      case 's': dbgSTP = 1; break;  // show #steps every STEPMASK+1 steps
      case 'x': memsize<<=1;break;  // double initial memory size
    }
  }
  mem   = reheap(NULL, memsize);
  gcmem = reheap(NULL, memsize);
  hp = NCOMB;
  u32 cl = 0;
  char filepath[FILEPATHLEN];
  const char *blcpath = getenv("BLCPATH");
  // after getopt call, optind is index of first non-option argument
  for (int qComp = optind < argc-1; optind < argc; optind++) {
    snprintf(filepath, FILEPATHLEN, "%s/%s.blc%s%s", blcpath, argv[optind], qBLC2?"2":"", mode?"8":"");
    fprintf(stderr, "Opening file %s\n", filepath);
    fp = fopen(filepath, "r");
    if (!fp) die("file not found.");
    u32 fcl = toCLK(db = qBLC2 ? parseBLC2() : parseBLC());
    nbits = 0;           // skip remaining bits in last lambda term byte
    if (qComp) {
      getbit(); nbits=0; // check for embedded input following lambda term
      if (inbits != EOF) die("program input gets misplaced in composition");
    }
    cl = !cl ? fcl : app(app('B',fcl), cl);
  }
  if (!cl) {
    fp = stdin;
    cl = toCLK(db = qBLC2 ? parseBLC2() : parseBLC());
    nbits = 0;           // skip remaining bits in last program byte
  }
  if (dbgProg) {
    if (db) showNL(db);
    showNL(cl);
   }
  clock_t start = clock();
  run(app(app(app(cl,app('-','?')), mode ? '>' : '+'),'V'));
  clock_t end = clock();
  u32 ms = (end - start) * 1000 / CLOCKS_PER_SEC;
  fprintf(stderr, "steps %u time %ums steps/s %uM #GC %u HP %u\n",
    steps, ms, ms ? steps/ms/1000 : 666, nGC, hp);
  return 0;
}
