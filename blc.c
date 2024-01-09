#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint32_t u32;

void die(char *s) { fprintf(stdout, "error: %s\n", s); exit(1); }

enum { FORWARD = '>', REDUCING = '<' }; // originally 27 9
enum { MEMSIZE = 1<<23, TABMAX = 1<<10, BUFMAX = 1<<20 };
u32 *mem, *gcmem, *sp, *spTop, hp, table[TABMAX], tabn; // just over 2GB

void stats() { printf("\n[Heap size %u, Stack size = %td]\n", hp, spTop - sp); }

static inline u32 isAddr(u32 n) { return n >= 128; }

u32 evac(u32 n) { // evacuate mem[n]`app`mem[n+1] to gcmem
  if (!isAddr(n)) return n;
  u32 x = mem[n]; u32 y = mem[n + 1];
  switch(x) {
    case FORWARD: return y;
    case REDUCING:
      mem[n] = FORWARD;
      mem[n + 1] = hp;
      hp += 2;
      return mem[n + 1];
    case 'I':
      mem[n] = REDUCING;
      y = evac(y);
      if (mem[n] == FORWARD) {
        fprintf(stdout, "\nREDUCING FORWARDED!\n");
        gcmem[mem[n + 1]] = 'I';
        gcmem[mem[n + 1] + 1] = y;
      } else {
        mem[n] = FORWARD;
        mem[n + 1] = y;
      }
      return mem[n + 1];
    default: break;
  }
  u32 z = hp;
  hp += 2;
  mem[n] = FORWARD;
  mem[n + 1] = z;
  gcmem[z] = x;
  gcmem[z + 1] = y;
  return z;
}

u32 gccount;
void gc(u32 ctr) {
  gccount++;
  fprintf(stdout, "\n%u GC %u -> ", ctr, hp - 128);
  hp = 128;
  u32 di = hp;
  sp = gcmem + MEMSIZE - 1;
  for (*sp = evac(*spTop); di < hp; ) {
    u32 x = gcmem[di] = evac(gcmem[di]);
    di++;
    if (x != '#') gcmem[di] = evac(gcmem[di]);
    di++;
  }
  fprintf(stdout, "%u\n", hp - 128);
  spTop = sp;
  u32 *tmp = mem;
  mem = gcmem;
  gcmem = tmp;
}

static inline u32 app(u32 f, u32 x) {
  u32 hp0 = hp;
  mem[hp++] = f;
  mem[hp++] = x;
  return hp0;
}

FILE *fp;
u32 fp_get() {
  u32 c = fgetc(fp);
  if (c == EOF) fclose(fp);
  return c;
}

u32 parseTerm() {
  u32 n, c;
  do c = fp_get(); while (c == '\n');
  switch(c) {
    case '`':
      c = parseTerm();
      return app(c, parseTerm());
    case '#': return app('#', fp_get());
    case '@': return table[fp_get() - ' '];
    case '(':
      n = 0;
      while ((c = fp_get()) != ')') n = 10*n + c - '0';
      return app('#', n);
    case '[':
      n = 0;
      while ((c = fp_get()) != ']') n = 10*n + c - '0';
      return table[n];
    default: return c;
  }
}

void putch(u32 c) { write(1,&c,1); }
u32 getch() { return getchar(); }

char *str;
u32 str_get() { u32 c = *(unsigned char*)str++; return c ? c : EOF; }

void parse() {
  hp = 128;
  tabn = 0;
  for(;;) {
    u32 c = parseTerm();
    if (c == EOF) {
      u32 root = table[tabn - 1];
      *(sp = spTop) = app(app(app(root,app('0','?')),'1'),'.');
      return;
    }
    if (tabn == TABMAX) die ("table overflow");
    table[tabn++] = c;
    if (fp_get() != ';') die("expected ';'");
  }
}

static inline u32 arg(u32 n) { return mem[sp [n] + 1]; }
static inline u32 num(u32 n) { return mem[arg(n) + 1]; }
static inline u32 apparg(u32 i, u32 j) { return app(arg(i), arg(j)); }
static inline void lazy(u32 delta, u32 f, u32 x) {
  sp += delta; u32 *p = mem + sp[1]; p[0] = f; p[1] = x;
}
void run() {
  gccount = 0;
  clock_t start = clock();
  u32 c, x;
  for(x = *sp;;) {
    static u32 ctr; if (++ctr == (1<<28)) { stats(); ctr = 0; }
    if (mem + hp > sp - 8) { gc(ctr);  x = *sp; }
    for (; isAddr(x); x = mem[x]) *sp-- = x;
    switch(x) {
      case FORWARD: stats(); die("stray forwarding pointer");
      case '.': {
        clock_t end = clock();
        fprintf(stdout, "\ngcs = %u, time = %lfms, HP = %u\n",
          gccount, (end - start) * 1000.0 / (double) CLOCKS_PER_SEC, hp);
        return;
      }
      case 'Y': lazy(0, x = arg(1), sp[1]); break;
      case 'S': c=arg(3); lazy(2, x = app(arg(1),c), app(arg(2),c)); break;
      case 'B': lazy(2, x = arg(1), apparg(2, 3)); break;
      case 'C': lazy(2, x = apparg(1, 3), arg(2)); break;
      case 'I': x = mem[*++sp + 1]; break;
      case 'K': x = mem[sp[1] + 1]; sp += 2; break;
      case 'F': x = mem[*(sp+=2) + 1]; break; // False, Nil
      case 'R': lazy(2, x = apparg(2, 3), arg(1)); break;
      case 'T': lazy(1, x = arg(2), arg(1)); break;
      case ':': lazy(2, x = apparg(3, 1), arg(2)); break;
      case '0': (c=getch())==EOF ? lazy(0,x = 'K','I') : lazy(0,x = app(':',app('#',c)),app('0','?')); break;
      case '#': lazy(1, x = arg(2), sp[1]); break;
      case '1': putch(num(1)); lazy(2, x = app(arg(2),'1'),arg(3)); break;
      case '=': num(1) == num(2) ? lazy(1, x = 'I', 'K') : lazy(1, x = 'K', 'I'); break;
      default: printf("?%u='%c'\n", x,x); stats(); die("unknown combinator");
    }
  }
}

int main(int argc, char **argv) {
    mem = malloc(MEMSIZE * sizeof(u32));
  gcmem = malloc(MEMSIZE * sizeof(u32));
  spTop = mem + MEMSIZE - 1;
  fp = fopen(argv[1], "r");
  if (!fp) die("fopen failed");
  parse();
  run();
  return 0;
}
