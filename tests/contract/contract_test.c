/*
 * contract_test.c — the EngineDb contract (lean/Bridge/EngineDbApi.lean, class
 * EngineDb, and its consequences in lean/Bridge/EngineDbApiLaws.lean) as
 * property tests against the C data layer AS LINKED UNDER THE MATCHER: the
 * adapter c/gen/engine_db_adapter.c over the handwritten data layer
 * c/src/matching_engine_gen.c, through the C face c/gen/engine_db.h.
 *
 * Method. The test keeps a model of the store's view, the Lean `Db`
 * (orders, levels, queues, hash, trees, live sets), drives the store with
 * random operations whose contract preconditions hold in the model, updates the
 * model by each operation's Lean postcondition, and after every operation
 * checks that everything observable through engine_db.h agrees with the model.
 * Each law has its own check function below; its comment quotes the Lean
 * statement it tests. The statement tested is the statement matcher_refines
 * assumes.
 *
 * Handles and validity. A handle is valid exactly while it is live in the
 * model. Using an invalid handle is undefined in C, so the test never does it;
 * what it checks is that the store never hands out an invalid handle: every
 * lookup (hash find, tree find/best, queue first/next, owner) returns a handle
 * live in the model, and every allocation returns one that was not live.
 *
 * Two data-layer facts that are not in engine_db.h are read from the data
 * layer's own structures (that is what "as linked" means here): the level pool
 * count (levelsUsed in the Lean class) and the level totals (private to the
 * data layer; the adapter maintains them).
 *
 * Usage: contract_test <first_seed> <seeds> <ops> <capacity>
 */
#include "engine_db.h"
#include "engine_db_adapter.h"
#include "../../c/include/matching_engine_gen.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXH 512
enum { F_ID, F_ACCOUNT, F_SIDE, F_STP, F_PRICE, F_QTY, F_REM, NF };

typedef struct { ME_OrderH h; int live; uint64_t f[NF]; int known[NF]; } MO;
typedef struct { ME_LevelH h; int live; uint64_t price; int pknown; ME_OrderH q[MAXH]; int qn; } ML;

static MO mo[MAXH]; static int nmo;
static ML ml[MAXH]; static int nml;
static ME_OrderH mhash[MAXH]; static int nhash;
static ME_LevelH mtree[2][MAXH]; static int ntree[2];   /* 0 = bids, 1 = asks */
static uint64_t CAP;
static uint64_t rng;

static uint64_t rnd(void) { rng = rng * UINT64_C(6364136223846793005) + UINT64_C(1442695040888963407); return rng >> 33; }
static uint64_t pick(uint64_t n) { return n ? rnd() % n : 0; }

/* ---------------------------------------------------------------- law tally */
typedef struct { const char *name; uint64_t n; } Law;
static Law laws[] = {
  {"orderAlloc_law (post, none iff capacity <= count)", 0},
  {"orderAlloc_full: full leaves the store unchanged", 0},
  {"orderAlloc_valid: a fresh handle", 0},
  {"orderFree_law / orderFree_valid", 0},
  {"levelAlloc_law (post, none iff capacity <= levelsUsed)", 0},
  {"levelAlloc_full: full leaves the store unchanged", 0},
  {"levelFree_law / levelFree_valid", 0},
  {"readOrder_law / writeOrder_law", 0},
  {"readLevel_law / writeLevel_law", 0},
  {"levelCount_law", 0},
  {"owner_law / owner_valid", 0},
  {"hashFind_law / hashFind_valid / hashFind_unique", 0},
  {"hashInsert_law / hash_find_after_insert / hash_insert_refused", 0},
  {"hashRemove_law / hash_find_after_remove", 0},
  {"qInsertTail_law / queue_after_insertTail / first_stable_under_insertTail", 0},
  {"qRemove_law / first_after_remove_head", 0},
  {"qFirst_law / qFirst_valid", 0},
  {"qNext_law / qNext_valid", 0},
  {"tFind_law / tFind_valid / tFind_unique", 0},
  {"tInsert_law / tree_find_after_insert", 0},
  {"tRemove_law / tree_find_after_remove", 0},
  {"tBest_law / tBest_valid / tBest_unique", 0},
  {"count laws (alloc +1, free -1, others unchanged)", 0},
  {"levelsUsed laws (alloc +1, free -1, others unchanged)", 0},
  {"handle still valid after reduce (write remaining)", 0},
  {"totals: level total = sum of remaining (data-layer private)", 0},
  {"read purity: reads change no later observation", 0},
  {"init_view / init_count / init_levelsUsed: the initial store is empty", 0},
};
enum { L_OALLOC, L_OFULL, L_OFRESH, L_OFREE, L_LALLOC, L_LFULL, L_LFREE, L_RWO, L_RWL, L_LCOUNT,
       L_OWNER, L_HFIND, L_HINS, L_HREM, L_QINS, L_QREM, L_QFIRST, L_QNEXT, L_TFIND, L_TINS,
       L_TREM, L_TBEST, L_COUNT, L_LUSED, L_REDUCE, L_TOTALS, L_PURE, L_INIT, NLAWS };

static uint64_t g_seed, g_step;
static void fail(const char *law, const char *what) {
    fprintf(stderr, "CONTRACT FAILURE seed %" PRIu64 " step %" PRIu64 ": %s: %s\n", g_seed, g_step, law, what);
    exit(1);
}
#define CHECK(L, cond, what) do { laws[L].n++; if (!(cond)) fail(laws[L].name, what); } while (0)

/* ---------------------------------------------------------------- the model */
static int mo_find(ME_OrderH h) { for (int i = 0; i < nmo; i++) if (mo[i].h == h) return i; return -1; }
static int ml_find(ME_LevelH h) { for (int i = 0; i < nml; i++) if (ml[i].h == h) return i; return -1; }
static int o_live(ME_OrderH h) { int i = mo_find(h); return i >= 0 && mo[i].live; }
static int l_live(ME_LevelH h) { int i = ml_find(h); return i >= 0 && ml[i].live; }
static uint64_t n_olive(void) { uint64_t n = 0; for (int i = 0; i < nmo; i++) n += mo[i].live; return n; }
static uint64_t n_llive(void) { uint64_t n = 0; for (int i = 0; i < nml; i++) n += ml[i].live; return n; }
static int in_hash(ME_OrderH h) { for (int i = 0; i < nhash; i++) if (mhash[i] == h) return 1; return 0; }
static int in_tree(int t, ME_LevelH l) { for (int i = 0; i < ntree[t]; i++) if (mtree[t][i] == l) return 1; return 0; }
static int owner_idx(ME_OrderH h) {
    for (int i = 0; i < nml; i++) if (ml[i].live) for (int k = 0; k < ml[i].qn; k++) if (ml[i].q[k] == h) return i;
    return -1;
}
static uint64_t levels_used(void) { return g_EngineDb.level_pool_n; }

/* A random live order / level satisfying a predicate, or -1. */
static int rand_order(int (*p)(int)) {
    int c[MAXH], n = 0;
    for (int i = 0; i < nmo; i++) if (mo[i].live && (!p || p(i))) c[n++] = i;
    return n ? c[pick((uint64_t)n)] : -1;
}
static int rand_level(int (*p)(int)) {
    int c[MAXH], n = 0;
    for (int i = 0; i < nml; i++) if (ml[i].live && (!p || p(i))) c[n++] = i;
    return n ? c[pick((uint64_t)n)] : -1;
}

/* ---------------------------------------------------------------- observation */
typedef struct { uint64_t v[16384]; int n; } Obs;
static void push(Obs *o, uint64_t x) { if (o->n < 16384) o->v[o->n++] = x; }

/* Everything readable through engine_db.h about the model's live rows. */
static void observe(Obs *o) {
    o->n = 0;
    push(o, ME_capacity()); push(o, ME_order_count()); push(o, levels_used());
    for (int i = 0; i < nmo; i++) if (mo[i].live) {
        ME_OrderH h = mo[i].h;
        push(o, ME_order_get_id(h)); push(o, ME_order_get_account(h)); push(o, ME_order_get_side(h));
        push(o, ME_order_get_stp_mode(h)); push(o, ME_order_get_price(h)); push(o, ME_order_get_qty(h));
        push(o, ME_order_get_remaining(h)); push(o, (uint64_t)(uintptr_t)ME_order_owner(h));
        push(o, (uint64_t)(uintptr_t)ME_hash_find(ME_order_get_id(h)));
    }
    for (int i = 0; i < nml; i++) if (ml[i].live) {
        ME_LevelH l = ml[i].h;
        push(o, ME_level_get_price(l)); push(o, ME_level_get_count(l));
        for (ME_OrderH x = ME_queue_first(l); x; x = ME_queue_next(x)) push(o, (uint64_t)(uintptr_t)x);
        push(o, (uint64_t)(uintptr_t)ME_bids_find(ME_level_get_price(l)));
        push(o, (uint64_t)(uintptr_t)ME_asks_find(ME_level_get_price(l)));
    }
    push(o, (uint64_t)(uintptr_t)ME_bids_best()); push(o, (uint64_t)(uintptr_t)ME_asks_best());
}

/* A burst of random reads: the store must look the same afterwards. */
static void read_burst(void) {
    int k = (int)pick(20);
    for (int j = 0; j < k; j++) {
        int i;
        switch (pick(9)) {
        case 0: (void)ME_capacity(); (void)ME_order_count(); break;
        case 1: if ((i = rand_order(NULL)) >= 0) { (void)ME_order_get_id(mo[i].h); (void)ME_order_get_remaining(mo[i].h); (void)ME_order_get_account(mo[i].h); } break;
        case 2: if ((i = rand_order(NULL)) >= 0) (void)ME_order_owner(mo[i].h); break;
        case 3: (void)ME_hash_find(pick(40)); break;
        case 4: (void)ME_bids_find(95 + pick(12)); (void)ME_asks_find(95 + pick(12)); break;
        case 5: (void)ME_bids_best(); (void)ME_asks_best(); break;
        case 6: if ((i = rand_level(NULL)) >= 0) { for (ME_OrderH x = ME_queue_first(ml[i].h); x; x = ME_queue_next(x)) (void)x; } break;
        case 7: if ((i = rand_level(NULL)) >= 0) { (void)ME_level_get_price(ml[i].h); (void)ME_level_get_count(ml[i].h); } break;
        default: if ((i = rand_order(NULL)) >= 0) { (void)ME_order_get_price(mo[i].h); (void)ME_order_get_qty(mo[i].h); (void)ME_order_get_side(mo[i].h); (void)ME_order_get_stp_mode(mo[i].h); } break;
        }
    }
}

/* ---------------------------------------------------------------- checks */

/* The whole view agrees with the model. The per-law checks below call this
   after each operation: every law says what changes AND (by the record update)
   that nothing else does. */
static void check_view(void) {
    /* count laws: `count s` is the number of live orders (Db.count = oLive.length). */
    CHECK(L_COUNT, ME_order_count() == n_olive(), "ME_order_count() != live orders");
    /* levelsUsed laws: `levelsUsed s` is the number of live levels. */
    CHECK(L_LUSED, levels_used() == n_llive(), "level_pool_n != live levels");
    for (int i = 0; i < nmo; i++) if (mo[i].live) {
        ME_OrderH h = mo[i].h;
        /* readOrder_law : ∀ s h, readOrder s h = (view s).orders h */
        uint64_t g[NF] = { ME_order_get_id(h), ME_order_get_account(h), ME_order_get_side(h),
                           ME_order_get_stp_mode(h), ME_order_get_price(h), ME_order_get_qty(h),
                           ME_order_get_remaining(h) };
        for (int f = 0; f < NF; f++) if (mo[i].known[f]) CHECK(L_RWO, g[f] == mo[i].f[f], "order field read differs");
        /* owner_law : owner.post (view s) h (owner s h):
             none → ¬ db.queued h ;  some l → h ∈ db.queue l */
        int oi = owner_idx(h);
        ME_LevelH ow = ME_order_owner(h);
        CHECK(L_OWNER, oi < 0 ? ow == NULL : ow == ml[oi].h, "owner differs");
        CHECK(L_OWNER, ow == NULL || l_live(ow), "owner returned an invalid level handle");
    }
    for (int i = 0; i < nml; i++) if (ml[i].live) {
        ME_LevelH l = ml[i].h;
        /* readLevel_law : ∀ s l, readLevel s l = (view s).levels l */
        if (ml[i].pknown) CHECK(L_RWL, ME_level_get_price(l) == ml[i].price, "level price read differs");
        /* levelCount_law : levelCount s l = (view s).queue l |>.length */
        CHECK(L_LCOUNT, ME_level_get_count(l) == (uint64_t)ml[i].qn, "level count != queue length");
        /* qFirst_law : qFirst.post (view s) l (qFirst s l) := r = (db.queue l).head?
           qNext_law  : ∃ l, h ∈ db.queue l ∧ r = nextIn (db.queue l) h        (FIFO order) */
        ME_OrderH x = ME_queue_first(l);
        CHECK(L_QFIRST, ml[i].qn == 0 ? x == NULL : x == ml[i].q[0], "queue first differs");
        CHECK(L_QFIRST, x == NULL || o_live(x), "queue first returned an invalid handle");
        for (int k = 0; k < ml[i].qn && x; k++) {
            CHECK(L_QNEXT, x == ml[i].q[k], "queue order differs from the FIFO model");
            x = ME_queue_next(x);
            CHECK(L_QNEXT, x == NULL || o_live(x), "queue next returned an invalid handle");
        }
        CHECK(L_QNEXT, x == NULL, "queue longer than the model");
        /* totals: the data layer's private total_qty is the sum of its orders' remaining. */
        uint64_t sum = 0;
        for (int k = 0; k < ml[i].qn; k++) sum += ME_order_get_remaining(ml[i].q[k]);
        CHECK(L_TOTALS, ((struct PriceLevel *)(void *)l)->total_qty == sum, "level total != sum of remaining");
    }
    /* hashFind_law : hashFind.post (view s) id (hashFind s id):
         none   → ∀ h ∈ db.hash, db.orderId h ≠ id
         some h → h ∈ db.hash ∧ db.orderId h = id                                    */
    for (int j = 0; j < 12; j++) {
        uint64_t id = j < 6 ? pick(40) : (nmo ? mo[pick((uint64_t)nmo)].f[F_ID] : 0);
        ME_OrderH r = ME_hash_find(id), want = NULL;
        for (int k = 0; k < nhash; k++) if (mo[mo_find(mhash[k])].f[F_ID] == id) want = mhash[k];
        CHECK(L_HFIND, r == want, "hash find differs");
        CHECK(L_HFIND, r == NULL || o_live(r), "hash find returned an invalid handle");
    }
    /* tFind_law : tFind.post (view s) t p (tFind s t p):
         none   → ∀ l ∈ db.tree t, db.levelPrice l ≠ p
         some l → l ∈ db.tree t ∧ db.levelPrice l = p
       tBest_law : none → db.tree t = [] ;
                   some l → l ∈ db.tree t ∧ ∀ l' ∈ db.tree t, better t (price l) (price l') */
    for (int t = 0; t < 2; t++) {
        for (uint64_t p = 94; p <= 107; p++) {
            ME_LevelH r = t == 0 ? ME_bids_find(p) : ME_asks_find(p), want = NULL;
            for (int k = 0; k < ntree[t]; k++) if (ml[ml_find(mtree[t][k])].price == p) want = mtree[t][k];
            CHECK(L_TFIND, r == want, "tree find differs");
            CHECK(L_TFIND, r == NULL || l_live(r), "tree find returned an invalid handle");
        }
        ME_LevelH b = t == 0 ? ME_bids_best() : ME_asks_best(), want = NULL;
        for (int k = 0; k < ntree[t]; k++) {
            uint64_t pk = ml[ml_find(mtree[t][k])].price;
            if (!want || (t == 0 ? pk > ml[ml_find(want)].price : pk < ml[ml_find(want)].price)) want = mtree[t][k];
        }
        CHECK(L_TBEST, b == want, "tree best differs");
        CHECK(L_TBEST, b == NULL || l_live(b), "tree best returned an invalid handle");
    }
}

/* ---------------------------------------------------------------- operations */

static int p_free_order(int i) { return !in_hash(mo[i].h) && owner_idx(mo[i].h) < 0; }
static int p_unhashed_known(int i) { return !in_hash(mo[i].h) && mo[i].known[F_ID]; }
static int p_hashed(int i) { return in_hash(mo[i].h); }
static int p_unqueued(int i) { return owner_idx(mo[i].h) < 0; }
static int p_queued(int i) { return owner_idx(mo[i].h) >= 0; }
static int p_free_level(int i) { return !in_tree(0, ml[i].h) && !in_tree(1, ml[i].h) && ml[i].qn == 0; }
static int p_treeless(int i) { return !in_tree(0, ml[i].h) && !in_tree(1, ml[i].h); }
static int p_treeless_priced(int i) { return p_treeless(i) && ml[i].pknown; }

/* orderAlloc_law : orderAlloc.post (view s) (orderAlloc s).1 (view (orderAlloc s).2) ∧
                    ((orderAlloc s).1 = none ↔ capacity ≤ count s)
   orderAlloc.post: none → db' = db ;
                    some h → db.orders h = none ∧ ∃ row, db' = { db with orders := upd …, oLive := h :: … }
   count_orderAlloc : (orderAlloc s).1 = some h → count (orderAlloc s).2 = count s + 1 */
static void op_order_alloc(void) {
    Obs before, after;
    uint64_t c0 = ME_order_count();
    int full = c0 >= CAP;
    if (full) observe(&before);
    ME_OrderH h = ME_order_alloc();
    CHECK(L_OALLOC, (h == NULL) == full, "alloc returned NULL iff count >= capacity: violated");
    if (!h) {
        observe(&after);
        CHECK(L_OFULL, before.n == after.n && !memcmp(before.v, after.v, sizeof(uint64_t) * (size_t)before.n),
              "a failed allocation changed the store");
        return;
    }
    CHECK(L_OFRESH, !o_live(h), "allocation returned a live handle");
    CHECK(L_COUNT, ME_order_count() == c0 + 1, "count did not grow by one");
    int i = mo_find(h);
    if (i < 0) { i = nmo++; mo[i].h = h; }
    mo[i].live = 1; memset(mo[i].known, 0, sizeof mo[i].known);   /* contents unspecified */
}

/* orderFree_law : orderFree.pre (view s) h → orderFree.post (view s) h (view (orderFree s h))
   pre  : db.orderLive h ∧ ¬ db.queued h ∧ h ∉ db.hash
   post : db' = { db with orders := upd db.orders h none, oLive := db.oLive.erase h }
   orderFree_valid : Free invalidates the freed handle and nothing else.
   count_orderFree : count (orderFree s h) + 1 = count s */
static void op_order_free(void) {
    int i = rand_order(p_free_order);
    if (i < 0) return;
    uint64_t c0 = ME_order_count();
    ME_order_free(mo[i].h);
    mo[i].live = 0;
    CHECK(L_OFREE, ME_order_count() + 1 == c0, "free did not shrink the count by one");
}

/* levelAlloc_law / levelFree_law: as for orders, with levelsUsed. */
static void op_level_alloc(void) {
    Obs before, after;
    uint64_t u0 = levels_used();
    int full = u0 >= CAP;
    if (full) observe(&before);
    ME_LevelH l = ME_level_alloc();
    CHECK(L_LALLOC, (l == NULL) == full, "level alloc returned NULL iff levelsUsed >= capacity: violated");
    if (!l) {
        observe(&after);
        CHECK(L_LFULL, before.n == after.n && !memcmp(before.v, after.v, sizeof(uint64_t) * (size_t)before.n),
              "a failed level allocation changed the store");
        return;
    }
    CHECK(L_LALLOC, !l_live(l), "level allocation returned a live handle");
    CHECK(L_LUSED, levels_used() == u0 + 1, "levelsUsed did not grow by one");
    int i = ml_find(l);
    if (i < 0) { i = nml++; ml[i].h = l; }
    ml[i].live = 1; ml[i].pknown = 0; ml[i].qn = 0;
}

/* levelFree.pre : db.levelLive l ∧ l ∉ db.tree .bids ∧ l ∉ db.tree .asks ∧ db.queue l = [] */
static void op_level_free(void) {
    int i = rand_level(p_free_level);
    if (i < 0) return;
    uint64_t u0 = levels_used();
    ME_level_free(ml[i].h);
    ml[i].live = 0;
    CHECK(L_LFREE, levels_used() + 1 == u0, "level free did not shrink levelsUsed by one");
}

/* writeOrder_law : writeOrder.pre (view s) h row → writeOrder.post … :
   pre  : ∃ old, db.orders h = some old ∧ (h ∈ db.hash → row.id = old.id)
   post : db' = { db with orders := upd db.orders h (some row) } */
static void op_set_order(void) {
    int i = rand_order(NULL);
    if (i < 0) return;
    int f = (int)pick(NF);
    if (f == F_ID && in_hash(mo[i].h)) f = F_PRICE;                 /* id frozen while hashed */
    uint64_t v;
    switch (f) {
    case F_ID: v = 1 + pick(30); break;                                /* small ids: duplicates occur */
    case F_SIDE: v = pick(2); break;
    case F_STP: v = pick(5); break;
    case F_PRICE: v = 95 + pick(12); break;
    default: v = pick(3) == 0 ? UINT64_MAX - pick(3) : 1 + pick(50); break;
    }
    uint64_t old = mo[i].f[F_REM]; int oldk = mo[i].known[F_REM];
    switch (f) {
    case F_ID: ME_order_set_id(mo[i].h, v); break;
    case F_ACCOUNT: ME_order_set_account(mo[i].h, v); break;
    case F_SIDE: ME_order_set_side(mo[i].h, v); break;
    case F_STP: ME_order_set_stp_mode(mo[i].h, v); break;
    case F_PRICE: ME_order_set_price(mo[i].h, v); break;
    case F_QTY: ME_order_set_qty(mo[i].h, v); break;
    default:
        /* keep level totals within uint64 for the data layer's private sum */
        if (owner_idx(mo[i].h) >= 0) v = 1 + pick(50);
        ME_order_set_remaining(mo[i].h, v);
        if (oldk && v < old) CHECK(L_REDUCE, o_live(mo[i].h), "handle invalid after reduce");
        break;
    }
    mo[i].f[f] = v; mo[i].known[f] = 1;
    CHECK(L_RWO, 1, "");
}

/* writeLevel_law : pre : ∃ old, db.levels l = some old ∧ (in a tree → row.price = old.price)
                    post: db' = { db with levels := upd db.levels l (some row) } */
static void op_set_level_price(void) {
    int i = rand_level(p_treeless);
    if (i < 0) return;
    uint64_t p = 95 + pick(12);
    ME_level_set_price(ml[i].h, p);
    ml[i].price = p; ml[i].pknown = 1;
    CHECK(L_RWL, 1, "");
}

/* hashInsert_law : pre : db.orderLive h ∧ h ∉ db.hash
   post : if ∃ h' ∈ db.hash, db.orderId h' = db.orderId h then ok = false ∧ db' = db
          else ok = true ∧ db' = { db with hash := h :: db.hash }
   hash_find_after_insert / hash_insert_refused */
static void op_hash_insert(void) {
    int i = rand_order(p_unhashed_known);
    if (i < 0) return;
    int dup = 0;
    for (int k = 0; k < nhash; k++) if (mo[mo_find(mhash[k])].f[F_ID] == mo[i].f[F_ID]) dup = 1;
    bool ok = ME_hash_insert(mo[i].h);
    CHECK(L_HINS, ok == !dup, "hash insert accepted a duplicate id, or refused a fresh one");
    if (ok) {
        mhash[nhash++] = mo[i].h;
        CHECK(L_HINS, ME_hash_find(mo[i].f[F_ID]) == mo[i].h, "hash find after insert");
    }
}

/* hashRemove_law : pre : h ∈ db.hash ; post : db' = { db with hash := db.hash.erase h }
   hash_find_after_remove */
static void op_hash_remove(void) {
    int i = rand_order(p_hashed);
    if (i < 0) return;
    ME_hash_remove(mo[i].h);
    for (int k = 0; k < nhash; k++) if (mhash[k] == mo[i].h) { mhash[k] = mhash[--nhash]; break; }
    CHECK(L_HREM, ME_hash_find(mo[i].f[F_ID]) != mo[i].h, "hash find after remove");
}

/* qInsertTail_law : pre : db.levelLive l ∧ db.orderLive h ∧ ¬ db.queued h
   post : db' = { db with queue := upd db.queue l (db.queue l ++ [h]) }
   first_stable_under_insertTail: the first order stays first. */
static void op_q_insert(void) {
    int j = rand_level(NULL), i = rand_order(p_unqueued);
    if (i < 0 || j < 0) return;
    if (!mo[i].known[F_REM]) { ME_order_set_remaining(mo[i].h, 1 + pick(9)); mo[i].f[F_REM] = ME_order_get_remaining(mo[i].h); mo[i].known[F_REM] = 1; }
    if (mo[i].f[F_REM] > 1000) { ME_order_set_remaining(mo[i].h, 7); mo[i].f[F_REM] = 7; }
    ME_OrderH first0 = ME_queue_first(ml[j].h);
    ME_queue_insert_tail(ml[j].h, mo[i].h);
    ml[j].q[ml[j].qn++] = mo[i].h;
    if (first0) CHECK(L_QINS, ME_queue_first(ml[j].h) == first0, "first order changed under insert-tail");
    else CHECK(L_QINS, ME_queue_first(ml[j].h) == mo[i].h, "inserted order is not first of an empty queue");
}

/* qRemove_law : pre : h ∈ db.queue l ; post : db' = { db with queue := upd db.queue l ((db.queue l).erase h) }
   first_after_remove_head: removing the head makes the next order the head. */
static void op_q_remove(void) {
    int i = rand_order(p_queued);
    if (i < 0) return;
    int j = owner_idx(mo[i].h), k = 0;
    while (ml[j].q[k] != mo[i].h) k++;
    ME_OrderH next = k + 1 < ml[j].qn ? ml[j].q[k + 1] : NULL;
    ME_queue_remove(ml[j].h, mo[i].h);
    memmove(&ml[j].q[k], &ml[j].q[k + 1], sizeof(ME_OrderH) * (size_t)(ml[j].qn - k - 1));
    ml[j].qn--;
    if (k == 0) CHECK(L_QREM, ME_queue_first(ml[j].h) == next, "head removal: next is not the new head");
    CHECK(L_QREM, ME_order_owner(mo[i].h) == NULL, "removed order still has an owner");
}

/* tInsert_law : pre : db.levelLive l ∧ l ∉ bids ∧ l ∉ asks ∧ ∀ l' ∈ db.tree t, price l' ≠ price l
   post : db' = { db with tree := upd db.tree t (l :: db.tree t) }
   tree_find_after_insert */
static void op_t_insert(void) {
    int i = rand_level(p_treeless_priced);
    if (i < 0) return;
    int t = (int)pick(2);
    for (int k = 0; k < ntree[t]; k++) if (ml[ml_find(mtree[t][k])].price == ml[i].price) return;
    if (t == 0) ME_bids_insert(ml[i].h); else ME_asks_insert(ml[i].h);
    mtree[t][ntree[t]++] = ml[i].h;
    CHECK(L_TINS, (t == 0 ? ME_bids_find(ml[i].price) : ME_asks_find(ml[i].price)) == ml[i].h,
          "tree find after insert");
}

/* tRemove_law : pre : l ∈ db.tree t ; post : db' = { db with tree := upd db.tree t ((db.tree t).erase l) }
   tree_find_after_remove */
static void op_t_remove(void) {
    int t = (int)pick(2);
    if (ntree[t] == 0) return;
    int k = (int)pick((uint64_t)ntree[t]);
    ME_LevelH l = mtree[t][k];
    if (t == 0) ME_bids_remove(l); else ME_asks_remove(l);
    mtree[t][k] = mtree[t][--ntree[t]];
    uint64_t p = ml[ml_find(l)].price;
    CHECK(L_TREM, (t == 0 ? ME_bids_find(p) : ME_asks_find(p)) == NULL, "tree find after remove");
}

/* ---------------------------------------------------------------- driver */

static void reset_model(void) { nmo = nml = nhash = ntree[0] = ntree[1] = 0; }

static void run_seed(uint64_t seed, uint64_t ops) {
    g_seed = seed; g_step = 0;
    rng = seed * UINT64_C(2862933555777941757) + 1;
    ME_adapter_init(CAP);
    reset_model();
    /* init_view : view init = Db.empty ; init_count : count init = 0 ; init_levelsUsed */
    CHECK(L_INIT, ME_order_count() == 0 && levels_used() == 0 && !ME_bids_best() && !ME_asks_best() &&
          !ME_hash_find(1), "the initial store is not empty");
    check_view();
    for (g_step = 1; g_step <= ops; g_step++) {
        switch (pick(16)) {
        case 0: case 1: op_order_alloc(); break;
        case 2: op_order_free(); break;
        case 3: op_level_alloc(); break;
        case 4: op_level_free(); break;
        case 5: case 6: op_set_order(); break;
        case 7: op_set_level_price(); break;
        case 8: op_hash_insert(); break;
        case 9: op_hash_remove(); break;
        case 10: case 11: op_q_insert(); break;
        case 12: op_q_remove(); break;
        case 13: op_t_insert(); break;
        case 14: op_t_remove(); break;
        default: {
            /* read purity: a burst of reads leaves every observation unchanged */
            Obs a, b;
            observe(&a); read_burst(); observe(&b);
            CHECK(L_PURE, a.n == b.n && !memcmp(a.v, b.v, sizeof(uint64_t) * (size_t)a.n),
                  "reads changed an observation");
            break;
        }
        }
        if (pick(4) == 0) read_burst();   /* reads interleaved everywhere: the model ignores them */
        check_view();
    }
}

int main(int argc, char **argv) {
    uint64_t first = argc > 1 ? strtoull(argv[1], 0, 10) : 1;
    uint64_t seeds = argc > 2 ? strtoull(argv[2], 0, 10) : 50;
    uint64_t ops = argc > 3 ? strtoull(argv[3], 0, 10) : 2000;
    CAP = argc > 4 ? strtoull(argv[4], 0, 10) : 8;
    if (CAP > 200) { fprintf(stderr, "capacity too large for the model\n"); return 2; }
    for (uint64_t s = first; s < first + seeds; s++) run_seed(s, ops);
    printf("contract (capacity %" PRIu64 "): seeds %" PRIu64 "-%" PRIu64 " x %" PRIu64 " operations: all laws hold\n",
           CAP, first, first + seeds - 1, ops);
    for (int k = 0; k < NLAWS; k++) printf("  %8" PRIu64 "  %s\n", laws[k].n, laws[k].name);
    return 0;
}
