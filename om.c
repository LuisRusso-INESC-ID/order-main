/*
 * om.c -- Order-maintenance structures (label-based, large universe).
 *
 * Implements, on a doubly linked list with a sentinel base node:
 *   naive : average of neighbours, global even relabel on collision
 *           (exponential-label baseline), universe 2^W for a chosen W.
 *   ds87  : Dietz-Sleator list-range relabeling: find the smallest j with
 *           w(x, x_j) > j^2 and respace x_1..x_{j-1}.          O(log n) am.
 *   bcdfz : Bender-Cole-Demaine-Farach-Colton-Zito tag-range relabeling
 *           with overflow threshold 1 < T < 2.                  O(log n) am.
 *   twolevel : one level of indirection: groups of <= G elements with
 *           local labels; groups are labelled by bcdfz.          O(1) am.
 *
 * Cost metric: number of label (re)assignments to existing elements
 * ("relabels"), plus wall-clock time.
 *
 * Author: Luis M. S. Russo (with Claude).  Public domain / CC0.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

/* ------------------------------------------------------------------ */
/* random numbers: splitmix64                                          */
static u64 rng_state = 0x9E3779B97F4A7C15ULL;
static inline u64 rnd(void) {
    u64 z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline u64 rndn(u64 n) { return rnd() % n; }

static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + 1e-9 * t.tv_nsec;
}

/* ------------------------------------------------------------------ */
/* list nodes                                                          */
typedef struct Node {
    struct Node *prev, *next;
    u64 label;            /* top label (group label in twolevel)      */
    u64 local;            /* local label (twolevel only)              */
    struct Node *group;   /* group record (twolevel only)             */
    int gsize;            /* number of elements, if this is a group   */
    struct Node *gfirst;  /* first element, if this is a group        */
} Node;

static u64 relabels = 0;

/* ================================================================== */
/* naive: universe [0, U), U = 2^W                                     */
typedef struct { Node base; u64 U; long n; } Naive;

static void naive_init(Naive *s, int W) {
    memset(s, 0, sizeof *s);
    s->U = (W >= 63) ? (1ULL << 62) : (1ULL << W);
    s->base.prev = s->base.next = &s->base;
    s->base.label = 0;
}
static void naive_relabel_all(Naive *s) {
    u64 gap = s->U / (u64)(s->n + 1); long i = 1;
    for (Node *p = s->base.next; p != &s->base; p = p->next, i++) {
        p->label = gap * (u64)i; relabels++;
    }
}
static void naive_insert(Naive *s, Node *x, Node *z) { /* z after x */
    z->prev = x; z->next = x->next; x->next->prev = z; x->next = z; s->n++;
    u64 lo = x->label, hi = (z->next == &s->base) ? s->U : z->next->label;
    if (hi - lo >= 2) { z->label = lo + (hi - lo) / 2; return; }
    naive_relabel_all(s); relabels--;  /* z's own label is not a relabel */
}

/* ================================================================== */
/* ds87: Dietz-Sleator.  Labels live in Z_M (M a power of two) on a
 * circular list that includes the base; the base may be relabeled too,
 * and order is decided by v(x) = (label(x) - label(base)) mod M.       */
typedef struct { Node base; u64 M; long n; } DS;

static void ds_init(DS *s, u64 M) {
    memset(s, 0, sizeof *s); s->M = M;
    s->base.prev = s->base.next = &s->base; s->base.label = 0;
}
/* forward distance from x to y in Z_M (M if y == x) */
static inline u64 ds_w(DS *s, Node *x, Node *y) {
    if (x == y) return s->M;
    return (y->label - x->label) & (s->M - 1);
}
static inline u64 ds_v(DS *s, Node *x) { return (x->label - s->base.label) & (s->M - 1); }
static void ds_insert(DS *s, Node *x, Node *z) {
    Node *y = x->next;
    if (ds_w(s, x, y) < 2) {
        Node *xj = y; u64 j = 1;   /* smallest j with w(x, x_j) > j^2 */
        while (xj != x && ds_w(s, x, xj) <= j * j) { xj = xj->next; j++; }
        u64 w = ds_w(s, x, xj);
        if (w <= 1) { fprintf(stderr, "ds87: universe too small\n"); exit(1); }
        Node *p = x->next; u64 k = 1;
        for (; p != xj; p = p->next, k++) {
            u64 nl = (x->label + (u64)((long double)w * k / j)) & (s->M - 1);
            if (nl != p->label) { p->label = nl; relabels++; }
        }
        y = x->next;
    }
    u64 g = ds_w(s, x, y);
    z->prev = x; z->next = y; y->prev = z; x->next = z; s->n++;
    z->label = (x->label + g / 2) & (s->M - 1);
}

/* ================================================================== */
/* bcdfz: tag ranges of size 2^i, threshold T.  Universe 2^B.          */
typedef struct { Node base; int B; double T; long n; double *tau; } BC;

static void bc_init(BC *s, int B, double T) {
    memset(s, 0, sizeof *s); s->B = B; s->T = T;
    s->base.prev = s->base.next = &s->base; s->base.label = 0;
    s->tau = malloc(sizeof(double) * (B + 1));
    for (int i = 0; i <= B; i++) s->tau[i] = pow(T, -i);
}
/* Insert z after x.  x may be base (insert at front). */
static void bc_link(BC *s, Node *x, Node *z) {
    z->prev = x; z->next = x->next; x->next->prev = z; x->next = z; s->n++;
}
static void bc_insert(BC *s, Node *x, Node *z) {
    u64 U = 1ULL << s->B;
    u64 lo = (x == &s->base) ? 0 : x->label;
    u64 hi = (x->next == &s->base) ? U : x->next->label;
    bc_link(s, x, z);
    if (x == &s->base && hi >= 2 && lo == 0) { z->label = hi / 2; if (z->label) return; }
    if (x != &s->base && hi - lo >= 2) { z->label = lo + (hi - lo) / 2; return; }
    /* relabel: z is temporarily unlabeled; it sits right after x.     */
    u64 c = (x == &s->base) ? 0 : x->label;   /* anchor tag            */
    Node *L = z, *R = z;          /* elements [L..R] are in range      */
    long cnt = 1;                 /* includes z                        */
    for (int i = 1; i <= s->B; i++) {
        u64 a = (i == 64) ? 0 : (c >> i) << i, b = a + (1ULL << i); /* [a,b) */
        while (L->prev != &s->base && L->prev->label >= a) { L = L->prev; cnt++; }
        while (R->next != &s->base && R->next->label < b) { R = R->next; cnt++; }
        if ((double)cnt <= s->tau[i] * (double)(1ULL << i) || i == s->B) {
            long double gap = (long double)(1ULL << i) / cnt;
            long k = 0;
            for (Node *p = L;; p = p->next, k++) {
                u64 nl = a + (u64)(gap * k);
                if (p == z) p->label = nl;
                else if (p->label != nl) { p->label = nl; relabels++; }
                if (p == R) break;
            }
            return;
        }
    }
}

/* ================================================================== */
/* twolevel: groups of <= G elements; group records live in a bcdfz.    */
typedef struct { BC top; int G; long n; Node *pool; long poolused, poolcap; } TL;

static Node *tl_newgroup(TL *s) {
    if (s->poolused == s->poolcap) { fprintf(stderr, "pool\n"); exit(1); }
    Node *g = &s->pool[s->poolused++]; memset(g, 0, sizeof *g); return g;
}
static void tl_init(TL *s, int G, long maxn) {
    memset(s, 0, sizeof *s); s->G = G;
    bc_init(&s->top, 62, 1.5);
    s->poolcap = maxn / (G / 2) + 16; s->pool = calloc(s->poolcap, sizeof(Node));
}
/* element list: elements are linked in global order via prev/next too.  */
static Node tl_head;  /* sentinel for the element list */

static void tl_spread(Node *g, Node *first, int k) { /* local labels */
    u64 gap = (1ULL << 62) / (u64)(k + 1); Node *p = first;
    for (int i = 1; i <= k; i++, p = p->next) {
        u64 nl = gap * (u64)i;
        if (p->local != nl || p->group != g) { relabels++; }
        p->local = nl; p->group = g;
    }
}
/* insert z after element x (x == &tl_head means front) */
static void tl_insert(TL *s, Node *x, Node *z) {
    Node *g;
    if (s->n == 0) {
        tl_head.next = tl_head.prev = &tl_head;
        g = tl_newgroup(s); bc_insert(&s->top, &s->top.base, g);
        z->prev = z->next = &tl_head; tl_head.next = tl_head.prev = z;
        g->gfirst = z; g->gsize = 1; z->group = g; z->local = 1ULL << 61;
        s->n = 1; return;
    }
    if (x == &tl_head) { g = tl_head.next->group; }
    else g = x->group;
    /* link into element list */
    z->prev = x; z->next = x->next; x->next->prev = z; x->next = z; s->n++;
    z->group = g; g->gsize++;
    if (x == &tl_head || x->group != g) g->gfirst = z;
    u64 lo = (z->prev == &tl_head || z->prev->group != g) ? 0 : z->prev->local;
    u64 hi = (z->next == &tl_head || z->next->group != g) ? (1ULL << 62) : z->next->local;
    if (hi - lo >= 2 && g->gsize <= s->G) { z->local = lo + (hi - lo) / 2; return; }
    if (g->gsize <= s->G) { tl_spread(g, g->gfirst, g->gsize); relabels--; return; }
    /* split group g into two halves; new group h after g in top list */
    int k1 = g->gsize / 2, k2 = g->gsize - k1;
    Node *p = g->gfirst; for (int i = 0; i < k1; i++) p = p->next;
    Node *h = tl_newgroup(s); bc_insert(&s->top, g, h);
    g->gsize = k1; h->gsize = k2; h->gfirst = p;
    tl_spread(g, g->gfirst, k1); tl_spread(h, p, k2); relabels--;
}
static inline int tl_order(Node *a, Node *b) {
    if (a->group != b->group) return a->group->label < b->group->label;
    return a->local < b->local;
}

/* ================================================================== */
/* driver                                                              */
enum { W_RANDOM, W_FRONT, W_SEQ, W_HOT };
static const char *wname[] = { "random", "front", "seq", "hot" };

static Node *elems;

static int verify_labels(Node *base) {
    for (Node *p = base->next; p->next != base; p = p->next)
        if (!(p->label < p->next->label)) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: om ALG N WORKLOAD [param] [seed] [bits]\n"
                        " ALG: naive ds87 bcdfz twolevel\n"
                        " WORKLOAD: random front seq hot\n");
        return 1;
    }
    const char *alg = argv[1]; long N = atol(argv[2]);
    int wl = 0; for (int i = 0; i < 4; i++) if (!strcmp(argv[3], wname[i])) wl = i;
    double param = argc > 4 ? atof(argv[4]) : 0;
    int bits = argc > 6 ? atoi(argv[6]) : 62;
    if (argc > 5) rng_state = strtoull(argv[5], 0, 10) * 0x9E3779B97F4A7C15ULL + 1;

    Node *nodes = calloc(N, sizeof(Node));
    elems = nodes;
    Naive na; DS ds; BC bc; TL tl;
    int A = !strcmp(alg, "naive") ? 0 : !strcmp(alg, "ds87") ? 1 :
            !strcmp(alg, "bcdfz") ? 2 : 3;
    if (A == 0) naive_init(&na, param > 0 ? (int)param : 62);
    if (A == 1) ds_init(&ds, 1ULL << bits);
    if (A == 2) bc_init(&bc, bits, param > 0 ? param : 1.5);
    if (A == 3) tl_init(&tl, param > 0 ? (int)param : 64, N);
    Node *base = A == 0 ? &na.base : A == 1 ? &ds.base : A == 2 ? &bc.base : &tl_head;

    long hot = 0;
    double t0 = now();
    for (long i = 0; i < N; i++) {
        Node *x;
        if (i == 0 || wl == W_FRONT) x = base;
        else if (wl == W_RANDOM) x = &nodes[rndn(i)];
        else if (wl == W_SEQ) x = &nodes[i - 1];
        else { if (i == 1) hot = 0; x = &nodes[hot]; } /* insert after a fixed element */
        Node *z = &nodes[i];
        if (A == 0) naive_insert(&na, x, z);
        else if (A == 1) ds_insert(&ds, x, z);
        else if (A == 2) bc_insert(&bc, x, z);
        else tl_insert(&tl, x, z);
    }
    double t1 = now();
    /* order queries */
    long Q = 1000000; volatile long acc = 0;
    double t2 = now();
    for (long q = 0; q < Q; q++) {
        Node *a = &nodes[rndn(N)], *b = &nodes[rndn(N)];
        if (A == 3) acc += tl_order(a, b);
        else if (A == 1) acc += ds_v(&ds, a) < ds_v(&ds, b);
        else acc += a->label < b->label;
    }
    double t3 = now();
    int ok;
    if (A == 3) {
        ok = 1; for (Node *p = tl_head.next; p->next != &tl_head; p = p->next)
            if (!tl_order(p, p->next)) { ok = 0; break; }
    } else if (A == 1) {
        ok = 1; for (Node *p = ds.base.next; p->next != &ds.base; p = p->next)
            if (!(ds_v(&ds, p) < ds_v(&ds, p->next))) { ok = 0; break; }
    } else ok = verify_labels(base);
    printf("%s %s %ld %g relabels_per_insert %.4f ns_per_insert %.1f ns_per_order %.1f ok %d\n",
           alg, wname[wl], N, param, (double)relabels / N, 1e9 * (t1 - t0) / N,
           1e9 * (t3 - t2) / Q, ok);
    return ok ? 0 : 2;
}
