/*
 * ll.c -- List labeling in the linear regime: n elements kept in sorted
 * order in an array of m = Theta(n) slots.  Cost = number of moves of
 * already-stored elements.
 *
 *   pma    : classical Itai-Konheim-Rodeh sparse table / packed-memory
 *            array: implicit tree, linear density thresholds.  O(log^2 n).
 *   hi     : randomized history-independent structure of Bender, Conway,
 *            Farach-Colton, Komlos, Kuszmaul, Wein (FOCS'22): recursive
 *            halving, pivot = minimum-hash element in a window of
 *            Theta(alpha/sqrt(log n)) ranks around the median.  O(log^1.5 n).
 *   seesaw : simplified See-Saw algorithm of Bender, Conway, Farach-Colton,
 *            Komlos, Koucky, Kuszmaul, Saks (FOCS'24): randomized rebuild
 *            windows, alternating learning/exploiting windows with
 *            history-dependent array skews, periodic resets, IKR leaves.
 *
 * Elements are identified by their insertion index; the list order is
 * defined by where they are inserted (z is inserted right after y).
 * Workloads are insertion-only (the setting of the See-Saw analysis):
 * start from m/4 evenly spaced elements, insert m/4 more.
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
static u64 rng_state = 0x1234567ULL;
static inline u64 rnd(void) {
    u64 z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline u64 mix(u64 z) {
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* ------------------------------------------------------------------ */
/* the array, positions, Fenwick tree over occupancy                   */
static long m;           /* number of slots */
static int *slot;        /* element id or -1 */
static long *pos;        /* slot of element */
static int *fen;         /* Fenwick tree, 1-based */
static int LOGM;
static u64 moves = 0;
static long nelem = 0;

static void fen_add(long i, int d) { for (i++; i <= m; i += i & -i) fen[i] += d; }
static long fen_prefix(long i) { /* number of occupied slots in [0, i) */
    long s = 0; for (; i > 0; i -= i & -i) s += fen[i]; return s;
}
static long fen_count(long a, long b) { return fen_prefix(b) - fen_prefix(a); }
static long fen_select(long k) { /* slot of the k-th element, k >= 1 */
    long p = 0;
    for (int b = LOGM; b >= 0; b--) {
        long q = p + (1L << b);
        if (q <= m && fen[q] < k) { p = q; k -= fen[q]; }
    }
    return p; /* 0-based slot */
}
static void place(int e, long s) { slot[s] = e; pos[e] = s; fen_add(s, 1); }
static void unplace(long s) { pos[slot[s]] = -1; slot[s] = -1; fen_add(s, -1); }

static void alloc_array(long M, long maxelems) {
    m = M; slot = malloc(sizeof(int) * m); for (long i = 0; i < m; i++) slot[i] = -1;
    pos = malloc(sizeof(long) * maxelems); memset(pos, 0xff, sizeof(long) * maxelems); fen = calloc(m + 1, sizeof(int));
    LOGM = 0; while ((1L << (LOGM + 1)) <= m) LOGM++;
}

/* buffer for collecting elements of a range */
static int *buf; static long bufcap;
static void ensure_buf(long k) {
    if (k > bufcap) { bufcap = 2 * k + 16; buf = realloc(buf, sizeof(int) * bufcap); }
}
/* Collect elements in [a,b) in order into buf[off..], inserting z right
 * after element y (y = -1 means before everything in the range,
 * y = -2 means z is not inserted). Returns count. */
static long collect(long a, long b, int y, int z, long off) {
    long k = off;
    if (y == -1) buf[k++] = z;
    for (long s = a; s < b; s++) if (slot[s] >= 0) {
        buf[k++] = slot[s];
        if (slot[s] == y) buf[k++] = z;
    }
    return k - off;
}
/* Write buf[off..off+k) evenly into [a,b); count moves of old elements.
 * Old elements must already have been removed from [a,b) by caller? No:
 * we clear the range first, then place. */
static int newelem = -1; /* element being inserted: placement not a move */
static void spread(long a, long b, long off, long k) {
    for (long s = a; s < b; s++) if (slot[s] >= 0) unplace(s);
    /* note: pos[] of elements now -1; we compare with remembered pos via
       oldpos array */
}
static long *oldpos;
static void clear_and_place(long a, long b, long off, long k, long *target) {
    for (long i = 0; i < k; i++) { int e = buf[off + i]; oldpos[e] = pos[e]; }
    for (long s = a; s < b; s++) if (slot[s] >= 0) unplace(s);
    for (long i = 0; i < k; i++) {
        int e = buf[off + i];
        if (e != newelem && oldpos[e] != target[i]) moves++;
        place(e, target[i]);
    }
}
static long *tgt; static long tgtcap;
static void ensure_tgt(long k) {
    if (k > tgtcap) { tgtcap = 2 * k + 16; tgt = realloc(tgt, sizeof(long) * tgtcap); }
}
static void even_targets(long a, long b, long k, long *t) {
    long L = b - a;
    for (long i = 0; i < k; i++) t[i] = a + (long)((double)i * L / k + 0.5 * L / k);
}
/* redistribute range [a,b) evenly, with z inserted after y (or y=-2) */
static void redistribute(long a, long b, int y, int z) {
    ensure_buf(b - a + 2);
    long k = collect(a, b, y, z, 0);
    ensure_tgt(k); even_targets(a, b, k, tgt);
    newelem = z; clear_and_place(a, b, 0, k, tgt); newelem = -1;
}

/* ================================================================== */
/* PMA on an arbitrary range [A,B): implicit tree by halving down to
 * segments of at most SEG slots; thresholds tau(d) linear from tauRoot at
 * depth 0 to tauLeaf=1 at the leaves.  Insert z right after y (y=-1:
 * z goes before all elements of the range; caller guarantees z belongs
 * to this range).  Returns 0 if the range itself cannot take z.        */
static long SEG = 32;
static int pma_insert_range(long A, long B, int y, int z, double tauRoot) {
    /* insertion point: slot index ip such that z goes right after slot
       ip-1 contents; for y=-1, ip = A */
    long ip = (y >= 0) ? pos[y] + 1 : A;
    /* build path of ranges */
    long ra[64], rb[64]; int d = 0;
    ra[0] = A; rb[0] = B;
    while (rb[d] - ra[d] > SEG) {
        long mid = ra[d] + (rb[d] - ra[d]) / 2;
        long a = ra[d], b = rb[d];
        /* the element y lives in the half containing ip-1 (if y>=0), else left */
        long key = (y >= 0) ? pos[y] : A;
        d++;
        if (key < mid) { ra[d] = a; rb[d] = mid; } else { ra[d] = mid; rb[d] = b; }
    }
    int h = d;
    /* leaf: try local shift */
    long la = ra[h], lb = rb[h];
    long cnt = fen_count(la, lb);
    if (cnt + 1 <= lb - la) {
        /* nearest empty slot to the right of insertion point within leaf */
        long s = (ip < la) ? la : ip;
        long r = s; while (r < lb && slot[r] >= 0) r++;
        if (r < lb) {
            for (long t = r; t > s; t--) { int e = slot[t - 1]; unplace(t - 1); place(e, t); moves++; }
            place(z, s); return 1;
        }
        long l = s - 1; while (l >= la && slot[l] >= 0) l--;
        /* shift (l, s-1] left by one, z goes to s-1 */
        for (long t = l; t < s - 1; t++) { int e = slot[t + 1]; unplace(t + 1); place(e, t); moves++; }
        place(z, s - 1); return 1;
    }
    for (int k = h - 1; k >= 0; k--) {
        double tau = (h == 0) ? 1.0 : tauRoot + (1.0 - tauRoot) * (double)k / h;
        long c = fen_count(ra[k], rb[k]);
        if (c + 1 <= tau * (rb[k] - ra[k]) || (k == 0 && c + 1 <= rb[k] - ra[k])) {
            redistribute(ra[k], rb[k], y, z); return 1;
        }
    }
    return 0;
}

/* ================================================================== */
/* HI: randomized history-independent list labeling (Zeno embedding)   */
static double EPS;        /* m = (1+EPS) n0 */
static long n0;           /* reference size; rebuilt when drifting */
static double SQRTL;
static u64 seed;
static long *Hlo, *Hhi; static int *Hpiv; /* per tree node; Hlo=-1: base */

static inline u64 hval(int e, int level) { return mix(((u64)e << 6 | (u64)level) ^ seed); }

/* window [lo,hi] (1-based ranks) for a node with s elements, range size L */
static void hi_window(long s, long L, long *lo, long *hi) {
    double ns = (double)n0 * L / m;
    double mu = s / ns;
    double alpha = EPS / 2 - fabs(1 - mu);
    if (alpha < 0) alpha = 0;
    double W = ns * alpha / SQRTL;
    long l = (long)ceil(s / 2.0 - W), h = (long)floor(s / 2.0 + W);
    if (l < 1) l = 1;
    if (h > s) h = s;
    if (h < l) { l = h = (s + 1) / 2; }
    *lo = l; *hi = h;
}
/* build node v over [a,b) at given level from buf[off..off+k), writing
 * targets into tgt[off..] */
static void hi_build(long v, long a, long b, int level, long off, long k) {
    long L = b - a;
    long lo, hi;
    if (k <= 0) { Hlo[v] = -1; return; }
    hi_window(k, L, &lo, &hi);
    if (hi - lo + 1 <= 4 || L < 2) {
        Hlo[v] = -1;
        for (long i = 0; i < k; i++) tgt[off + i] = a + (long)((double)i * L / k + 0.5 * L / k);
        return;
    }
    long best = lo; u64 bh = hval(buf[off + lo - 1], level);
    for (long r = lo + 1; r <= hi; r++) {
        u64 hv = hval(buf[off + r - 1], level);
        if (hv < bh) { bh = hv; best = r; }
    }
    long mid = a + L / 2;
    long kl = best, kr = k - best;
    if (kl > mid - a || kr > b - mid) { /* safety: should not happen */
        Hlo[v] = -1;
        for (long i = 0; i < k; i++) tgt[off + i] = a + (long)((double)i * L / k + 0.5 * L / k);
        return;
    }
    Hlo[v] = lo; Hhi[v] = hi; Hpiv[v] = buf[off + best - 1];
    hi_build(2 * v, a, mid, level + 1, off, kl);
    hi_build(2 * v + 1, mid, b, level + 1, off + kl, kr);
}
static void hi_rebuild(long v, long a, long b, int level, int y, int z) {
    ensure_buf(b - a + 2); ensure_tgt(b - a + 2);
    long k = collect(a, b, y, z, 0);
    hi_build(v, a, b, level, 0, k);
    newelem = z; clear_and_place(a, b, 0, k, tgt); newelem = -1;
}
static void hi_global_rebuild(int y, int z) {
    long k = nelem + (z >= 0 ? 1 : 0);
    n0 = k; hi_rebuild(1, 0, m, 0, y, z);
}
/* element of the node [a,b) with (current, pre-insertion) rank r */
static int rank_elem(long a, long r) { return slot[fen_select(fen_prefix(a) + r)]; }

static void hi_insert(int y, int z) {
    if (fabs((double)(nelem + 1) - n0) > EPS * n0 / 4) { hi_global_rebuild(y, z); nelem++; return; }
    long v = 1, a = 0, b = m; int level = 0;
    for (;;) {
        long s = fen_count(a, b);           /* old size */
        long sn = s + 1;
        /* rank of z among new set: (#elements of range at or before y) + 1 */
        long rx = 1;
        if (y >= 0 && pos[y] >= a) rx = fen_count(a, (pos[y] < b ? pos[y] + 1 : b)) + 1;
        long lo2, hi2; hi_window(sn, b - a, &lo2, &hi2);
        int rebuild = 0;
        if (Hlo[v] < 0 || hi2 - lo2 + 1 <= 4 || b - a < 2) rebuild = 1;
        long rp = 0;
        if (!rebuild) {
            int p = Hpiv[v];
            long rpo = fen_count(a, pos[p] + 1);
            rp = rpo + (rpo >= rx);
            if (rp < lo2 || rp > hi2) rebuild = 1;
            else {
                u64 best = hval(p, level);
                if (rx >= lo2 && rx <= hi2 && hval(z, level) < best) rebuild = 1;
                long olo = Hlo[v], ohi = Hhi[v];
                long mlo = olo + (olo >= rx), mhi = ohi + (ohi >= rx);
                for (long r = lo2; r <= hi2 && !rebuild; r++) {
                    if (r == rx) continue;
                    if (r >= mlo && r <= mhi) continue;  /* was in old window */
                    long ro = r - (r > rx);
                    int e = rank_elem(a, ro);
                    if (hval(e, level) < best) rebuild = 1;
                }
                /* elements inside [mlo,mhi] but shifted: none new.  If the
                   hole rx lies inside, mapped set excludes rx only: fine. */
            }
        }
        if (rebuild) {
            int yy = (y >= 0 && pos[y] >= a) ? y : -1;
            hi_rebuild(v, a, b, level, yy, z); nelem++; return;
        }
        long lo, hi; lo = lo2; hi = hi2;
        Hlo[v] = lo; Hhi[v] = hi;
        long mid = a + (b - a) / 2;
        if (rx < rp) { v = 2 * v; b = mid; } else { v = 2 * v + 1; a = mid; }
        level++;
        /* if y is outside the child range, z goes to the child's front */
    }
}

/* ================================================================== */
/* SEE-SAW (simplified, faithful structure; tunable alpha, beta).      */
typedef struct SNode {
    long a, b;                 /* subarray */
    int leaf;                  /* 1 = tiny/expensive leaf (IKR inside) */
    struct SNode *L, *R;
    long w, wcnt, D, quota; int j;
} SNode;
static double SALPHA = 16, SBETA = 8;
static long TINY = 32;
static int KMAX;
static u64 fallbacks = 0, resets = 0, wrebuilds = 0;

static int draw_K(void) {
    /* p_k = 2^{-(k+1)} (1 + k/kmax), k>=1; p_0 = rest */
    double u = rndu(), acc = 0;
    for (int k = 1; k <= KMAX; k++) {
        acc += pow(2, -(k + 1)) * (1.0 + (double)k / KMAX);
        if (u < acc) return k;
    }
    return 0;
}
static void ss_free(SNode *t) { if (!t) return; ss_free(t->L); ss_free(t->R); free(t); }

/* create a balanced subtree over [a,b) whose elements are already placed
 * (evenly) in the range.  mL/mR halves. */
static SNode *ss_create(long a, long b) {
    SNode *t = calloc(1, sizeof *t); t->a = a; t->b = b;
    long L = b - a, c = fen_count(a, b);
    if (L <= TINY || (double)c / L > 0.75) { t->leaf = 1; return t; }
    int K = draw_K();
    t->w = (long)(L / (SALPHA * pow(2, K))); if (t->w < 1) t->w = 1;
    t->quota = (long)(L / SALPHA); if (t->quota < 1) t->quota = 1;
    t->j = 1; t->wcnt = 0; t->D = 0;
    long mid = a + L / 2;
    t->L = ss_create(a, mid); t->R = ss_create(mid, b);
    return t;
}
/* balanced rebuild of t's range including z after y (y may be -2) */
static SNode *ss_reset(SNode *t, int y, int z) {
    long a = t->a, b = t->b; ss_free(t);
    redistribute(a, b, y, z);
    return ss_create(a, b);
}
/* window-boundary rebuild with skew Q: left child gets the old left
 * child's elements in [a, a+mL), right child gets the rest. */
static void ss_window_rebuild(SNode *t) {
    long a = t->a, b = t->b, L = b - a;
    long mid_old = t->L->b;
    long cl = fen_count(a, mid_old), cr = fen_count(mid_old, b);
    long Q = 0;
    if (t->j % 2 == 0) {  /* exploiting window: skew from previous window's D */
        Q = (long)((double)L * t->D / (SBETA * t->w));
        long lim = (long)(L / SBETA); if (Q > lim) Q = lim; if (Q < -lim) Q = -lim;
    }
    long mL = L / 2 - Q;
    /* keep both children at density <= 0.8 */
    if (cl > 0.8 * mL) mL = (long)ceil(cl / 0.8);
    if (cr > 0.8 * (L - mL)) mL = L - (long)ceil(cr / 0.8);
    if (mL < 1) mL = 1;
    if (mL > L - 1) mL = L - 1;
    ss_free(t->L); ss_free(t->R);
    /* redistribute each side evenly */
    ensure_buf(L + 2); ensure_tgt(L + 2);
    long k = collect(a, b, -2, -1, 0);
    even_targets(a, a + mL, cl, tgt); even_targets(a + mL, b, cr, tgt + cl);
    (void)k; clear_and_place(a, b, 0, cl + cr, tgt);
    t->L = ss_create(a, a + mL); t->R = ss_create(a + mL, b);
    wrebuilds++;
}
static SNode *sroot;
/* insert z after y into subtree t; returns new subtree root (may change) */
static SNode *ss_insert(SNode *t, int y, int z) {
    if (t->leaf) {
        if (pma_insert_range(t->a, t->b, y, z, 0.9)) return t;
        fallbacks++;
        return NULL; /* caller rebuilds */
    }
    if (--t->quota <= 0) { resets++; return ss_reset(t, y, z); }
    if (t->wcnt >= t->w) {          /* window boundary */
        ss_window_rebuild(t);
        t->j++; t->wcnt = 0; t->D = 0;
    }
    /* route: left if L nonempty and max(L) > z */
    long cl = fen_count(t->L->a, t->L->b);
    int left = 0;
    if (cl > 0) {
        long lastL = fen_select(fen_prefix(t->L->a) + cl);
        if (y < 0 || pos[y] < lastL) left = 1;
    }
    /* y == -1 here means z goes before all elements of this range */
    int yy = y;
    if (!left && y >= 0 && pos[y] < t->R->a) yy = -1;  /* z first in R */
    if (left && y >= 0 && pos[y] < t->L->a) yy = -1;
    t->wcnt++; t->D += left ? -1 : 1;
    SNode *c = left ? t->L : t->R;
    SNode *r = ss_insert(c, yy, z);
    if (r == NULL) {
        /* child could not absorb: rebuild this node from scratch */
        return ss_reset(t, y, z);
    }
    if (left) t->L = r; else t->R = r;
    return t;
}

/* ================================================================== */
static int verify(void) {
    /* elements must appear in list order: we track order with an explicit
       rank array maintained by a linked list */
    return 1;
}

/* linked list of elements for verification */
static int *nxt;

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: ll ALG LOGM WORKLOAD [seed] [p1] [p2]\n"
                        " ALG: pma hi seesaw\n WORKLOAD: random front hot seq\n");
        return 1;
    }
    const char *alg = argv[1]; int lg = atoi(argv[2]); const char *wl = argv[3];
    u64 sd = argc > 4 ? strtoull(argv[4], 0, 10) : 1;
    rng_state = sd * 0x9E3779B97F4A7C15ULL + 7; seed = mix(sd + 99);
    double p1 = argc > 5 ? atof(argv[5]) : 0, p2 = argc > 6 ? atof(argv[6]) : 0;
    long M = 1L << lg;
    long ninit = M / 4, nins = M / 4, total = ninit + nins;
    alloc_array(M, total + 2);
    oldpos = malloc(sizeof(long) * (total + 2));
    nxt = malloc(sizeof(int) * (total + 2));
    SEG = 1; while (SEG < lg) SEG <<= 1;  /* segment ~ log m, power of two */
    int A = !strcmp(alg, "pma") ? 0 : !strcmp(alg, "hi") ? 1 : 2;
    /* initial elements 0..ninit-1 evenly spaced, list order = id order */
    for (long i = 0; i < ninit; i++) place((int)i, (long)((double)i * M / ninit + 0.5 * M / ninit));
    for (long i = 0; i < ninit; i++) nxt[i] = (i + 1 < ninit) ? (int)(i + 1) : -1;
    int head = 0;
    nelem = ninit;
    double tauRoot = 0.6;
    if (A == 0 && p1 > 0) tauRoot = p1;
    if (A == 1) {
        EPS = (double)M / total - 1.0;      /* final density 1/2 => eps = 1 */
        if (p1 > 0) EPS = p1;
        SQRTL = sqrt((double)lg);
        Hlo = malloc(sizeof(long) * 2 * M); Hhi = malloc(sizeof(long) * 2 * M);
        Hpiv = malloc(sizeof(int) * 2 * M);
        n0 = ninit; hi_rebuild(1, 0, M, 0, -2, -1); moves = 0;
    }
    if (A == 2) {
        double ll = log2((double)lg);
        KMAX = (int)ceil(2 * ll); if (KMAX < 1) KMAX = 1;
        if (p1 > 0) SALPHA = p1;
        if (p2 > 0) SBETA = p2;
        TINY = (long)pow(2, sqrt((double)lg)); if (TINY < 16) TINY = 16;
        if (getenv("SS_TINY_ALPHA")) { long t = (long)(atof(getenv("SS_TINY_ALPHA")) * SALPHA); if (t > TINY) TINY = t; }
        sroot = ss_create(0, M);
    }
    clock_t c0 = clock();
    int hot = (int)(ninit / 2);
    for (long i = 0; i < nins; i++) {
        int z = (int)(ninit + i);
        int y;
        if (!strcmp(wl, "random")) { y = (int)(rnd() % (u64)(nelem + 1)) - 1; if (y >= 0) y = (y < ninit + i) ? y : -1; }
        else if (!strcmp(wl, "front")) y = -1;
        else if (!strcmp(wl, "hot")) y = hot;           /* always right after a fixed element */
        else y = (i == 0) ? hot : z - 1;                 /* sequential after hot */
        if (A == 0) { if (!pma_insert_range(0, M, y, z, tauRoot)) { fprintf(stderr, "full\n"); return 1; } nelem++; }
        else if (A == 1) hi_insert(y, z);
        else {
            SNode *r = ss_insert(sroot, y, z);
            if (r == NULL) { sroot = ss_reset(sroot, y, z); } else sroot = r;
            nelem++;
        }
        /* maintain list for verification */
        if (y < 0) { nxt[z] = head; head = z; } else { nxt[z] = nxt[y]; nxt[y] = z; }
    }
    double secs = (double)(clock() - c0) / CLOCKS_PER_SEC;
    /* verify: walking the list must visit increasing positions */
    int ok = 1; long cnt = 0; long last = -1;
    for (int e = head; e >= 0; e = nxt[e]) { if (pos[e] <= last) { ok = 0; break; } last = pos[e]; cnt++; }
    if (cnt != total || fen_count(0, M) != total) ok = 0;
    printf("%s %s %d moves_per_insert %.4f us_per_insert %.3f ok %d", alg, wl, lg,
           (double)moves / nins, 1e6 * secs / nins, ok);
    if (A == 2) printf(" resets %llu wrebuilds %llu fallbacks %llu", (unsigned long long)resets,
                       (unsigned long long)wrebuilds, (unsigned long long)fallbacks);
    printf("\n");
    (void)verify; (void)spread;
    return ok ? 0 : 2;
}
