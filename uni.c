// Binary Lambda Calculus universal machine heavily based on Ben Lynn's
// ION machine at https://crypto.stanford.edu/~blynn/compiler/ION.html
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <getopt.h>
#include <time.h>

typedef uint32_t u32;
enum { MINMEMSZ = 1<<20, MAXMEMSZ = 1<<29 };
u32 memsize, *mem, *gcmem, *sp, *spTop, hp, dbgGC, dbgCL, dbgSTP;
void die(char *s) { fprintf(stderr, "error: %s\n", s); exit(1); }
static inline u32 isComb(u32 n) { return n < 128; }
static inline u32 app(u32 f, u32 x) { mem[hp] = f; mem[hp+1] = x; return (hp+=2)-2; }

u32 evac(u32 n) {
  if (isComb(n)) return n;
  u32 x = mem[n];
  u32 y = mem[x];
  while (y == 'T') {
    mem[n] = y = mem[n+1];
    mem[n+1] = mem[x+1];
    y = mem[x = y];
  }
  if (y == 'K') {
    mem[n+1] = mem[x+1];
    x = mem[n] = 'I';
  }
  y = mem[n + 1];
  if (!x) return y;
  if (!y) die("Cyclic!");
  if (x == 'I') {
    mem[n] = mem[n+1] = 0;
    return mem[n+1] = evac(y);
  }
  gcmem[hp] = x; gcmem[hp+1] = y;
    mem[ n] = 0;   mem[ n+1] = hp;
  return (hp += 2) - 2;
}

u32 steps, nGC, qDblMem;
void gc() {
  nGC++;
  if (dbgGC) fprintf(stderr, "\nmemsize %u steps %u GC %u -> ", memsize, steps, hp - 128);
  if (qDblMem) {
    memsize *= 2;
    gcmem = realloc(gcmem, memsize * sizeof(u32));
    if (!gcmem) die("realloc failed");
    memset(gcmem, 0, 128);
  }
  sp = gcmem + memsize-1;
  u32 di = hp = 128;
  for (*sp = evac(*spTop); di < hp; di++)
    gcmem[di] = evac(gcmem[di]);
  if (dbgGC) fprintf(stderr, "%u\n", hp - 128);
  spTop = sp;
  u32 *old = mem;
  mem = gcmem;
  gcmem = old;
  if (qDblMem) {
    gcmem = realloc(gcmem, memsize * sizeof(u32));
    if (!gcmem) die("realloc failed");
    memset(gcmem, 0, 128);
  }
  qDblMem = hp >= memsize/2 && memsize < MAXMEMSZ;
}

u32 nbits, inbits, mode; // bit mode 0 byte mode 7
u32 getbit() {
  if (!nbits) { nbits = mode; inbits = getchar(); } else nbits--;
  return (inbits>>nbits) & 1;
}
u32 parseBLC() {
  u32 x;
  if (getbit()) { // variable
    for (x=0; getbit(); x++) { }
    return app('V', x);
  }
  u32 isApp = getbit();
  x = parseBLC();
  return isApp ? app(x, parseBLC()) : app('L', x); // application : abstraction
}

// does CL term have an occurance of Var 0?
u32 hasVar0(u32 cl) {
  if (isComb(cl)) return 0;
  u32 f = mem[cl], a = mem[cl+1];
  return f == 'V' ? a == 0 : hasVar0(f) || hasVar0(a);
}
// decrease variable depth
u32 drip(u32 cl) {
  if (isComb(cl)) return cl;
  u32 f = mem[cl], a = mem[cl+1];
  return f == 'V' ? app('V', a - 1) :  app(drip(f),drip(a));
}
// bracket abstraction; sorry, no Kiselyov :-( yet :-)
u32 abstract(u32 cl) {
  if (isComb(cl)) return cl == 'I' ? 'F' : app('K',cl);
  u32 f = mem[cl], a = mem[cl+1];
  if (f == 'V') return a==0 ? 'I' : app('K',app('V', a-1));
  switch (2 * hasVar0(f) + hasVar0(a)) {
    case 0: return app('K', drip(cl));
    case 1: f = drip(f);
            if (mem[a] == 'V') return f;
            a = abstract(a);
            return f=='C' && a=='T' ? ':' : app(app('B',f),a);
    case 2: f = abstract(f);
            return app(f=='I' ? 'T' : f=='C' ? 'R' : app('C',f),drip(a));
    case 3: f = abstract(f); a = abstract(a);
            return f=='I' && a=='I' ? 'D' : app(app('S',f),a);
  }
  return 0;
}

// if DB term has all occurances of Var n doubled, return undoubled version, else return 0
u32 unDoubleVar(u32 n, u32 db) {
  u32 udf, f = mem[db];
  if (f == 'V') return db;
  u32 uda, a = mem[db+1];
  if (f == 'L') return (uda = unDoubleVar(n+1,a)) ? app('L', uda) : 0;
  u32 qf = mem[f]=='V' && mem[f+1]==n;
  u32 qa = mem[a]=='V' && mem[a+1]==n;
  if (qf && qa) return app('V',n);
  if (qf || qa) return 0;
  return (udf = unDoubleVar(n,f)) && (uda = unDoubleVar(n,a)) ? app(udf,uda) : 0;
}
// convert de-bruijn lambda term to combinatory logic term
u32 toCL(u32 db) {
  u32 f = mem[db];
  if (f == 'V') return db;
  u32 a = mem[db+1], aCL = toCL(a);
  if (f == 'L') return abstract(aCL);
  u32 fCL = toCL(f);
  return fCL=='D' && mem[a]=='L' && mem[a=mem[a+1]]!='V' && (a=unDoubleVar(0,a))
    ? app(app('Y',app('S','I')),toCL(app('L',a))) // application to SI benefits GC
    : app(fCL,aCL);
}

void putch(u32 c) { putchar(c); fflush(stdout); }
void show(u32 n) {
  if (!isComb(n)) {
    u32 f = mem[n], a = mem[n+1];
    if (f == 'V') putch('0'+a);
    else if (f == 'L') { putch('\\'); show(a); }
    else { putch('`'); show(f); show(a); }
  } else putch(n);
}
void stats() { printf("\nsteps %u heap %u stack %td\n", steps, hp, spTop - sp); }
static inline u32 arg(u32 n) { return mem[sp [n] + 1]; }
static inline u32 apparg(u32 i, u32 j) { return app(arg(i), arg(j)); }
static inline void lazy(u32 delta, u32 f, u32 x) {
  sp += delta; u32 *p = mem + sp[1]; p[0] = f; p[1] = x;
}
void run(u32 x) {
  *(sp = spTop = mem + memsize - 1) = x;
  char outbits = 0;
  for (steps = nGC = 0; ; steps++) {
    if (dbgSTP && !(steps & (1<<28)-1)) stats();
    if (mem + hp > sp - 8) { gc(); x = *sp; }
    for (; !isComb(x); x = mem[x]) *sp-- = x;
    switch (x) {
      case 'D': x = arg(1); break;
      case 'I': x = mem[*++sp + 1]; break;
      case 'Y': lazy(0, x = arg(1), sp[1]); break;
      case '+': lazy(0, x = app(arg(1),'0'), '1'); break; // output bits
      case '>': lazy(0, x = app(arg(1),'+'), '!'); break; // output bytes
      case 'K': lazy(1, x = 'I', arg(1)); break;
      case 'F': lazy(1, x = 'I', arg(2)); break;
      case 'T': lazy(1, x = arg(2), arg(1)); break;
      case 'B': lazy(2, x = arg(1), apparg(2, 3)); break;
      case 'C': lazy(2, x = apparg(1, 3), arg(2)); break;
      case 'R': lazy(2, x = apparg(2, 3), arg(1)); break;
      case ':': lazy(2, x = apparg(3, 1), arg(2)); break;
      case 'S': lazy(2, x = apparg(1,3), apparg(2,3)); break;
      case '0': case '1': if (mode) outbits = outbits<<1 | (x&1);
                          else putch(x);                  // output bit
                lazy(0, x = arg(1), '+'); break;
      case '!': putch(outbits);                           // output byte
                lazy(0, x = arg(1), '>'); break;
      case '-': getbit(); nbits++;                        // input
                if (inbits == EOF) { lazy(0, x = 'K', 'I'); break; }
                if (mode) {
                  for (x='F'; nbits; nbits--,inbits>>=1)
                    x = app(app(':', "KF"[inbits&1]), x);
                } else x = "KF"[getbit()];
                lazy(0, x = app(':', x), app('-','?')); break;
      case '.': return;                                   // end-of-output
      default: die("unknown combinator");
    }
  }
}

int main(int argc, char **argv) {
  dbgGC = dbgCL = dbgSTP = qDblMem = nbits = 0;
  mode = 7;
  int opt;
  while ((opt = getopt(argc, argv, "bgcs")) != -1) {
    switch (opt) {
      case 'b': mode = 0; break;
      case 'g': dbgGC = 1; break;
      case 'c': dbgCL = 1; break;
      case 's': dbgSTP = 1; break;
    }
  }
  mem = malloc((memsize = MINMEMSZ) * sizeof(u32));
  gcmem = malloc(memsize * sizeof(u32));
  if (!mem || !gcmem) die("malloc failed");
  memset(mem, 0, 128); // allow mem[x]=='C' test without !isComb(x)
  memset(gcmem, 0, hp = 128);
  u32 db = parseBLC();
  nbits = 0;            // skip remaining bits in last program byte
  u32 cl = toCL(db);
  if (dbgCL) { show(db); putch('\n'); show(cl); putch('\n'); }
  clock_t start = clock();
  run(app(app(app(cl, app('-','?')), mode ? '>' : '+'),'.'));
  clock_t end = clock();
  u32 ms = (end - start) * 1000 / CLOCKS_PER_SEC;
  fprintf(stderr, "\nsteps %u time %ums steps/s %uM #GC %u HP %u\n",
    steps, ms, ms ? steps/ms/1000 : 666, nGC, hp);
  return 0;
}
