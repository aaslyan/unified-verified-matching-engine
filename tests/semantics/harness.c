/*
 * harness.c — runs one generated program (tests/semantics) in C and prints its
 * outcome in the format of lean/Matcher/SemTest.lean:
 *   ok <value> <order count> [<maker>,<taker>,<price>,<qty> ...]
 *   trap <class>
 * The program is compiled with -DME_TRAP_REPORT=harness_trap, so me_trap(k)
 * reports its class here before stopping.
 */
#include "engine_db.h"
#include "engine_db_adapter.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

uint64_t t_main(void);

void harness_trap(unsigned k);
void harness_trap(unsigned k) {
    printf("trap %u\n", k);
    fflush(stdout);
    _Exit(0);
}

int main(int argc, char **argv) {
    uint64_t cap = argc > 1 ? strtoull(argv[1], 0, 10) : 3;
    ME_adapter_init(cap);
    uint64_t v = t_main();
    printf("ok %" PRIu64 " %" PRIu64 " [", v, ME_order_count());
    for (uint64_t i = 0; i < ME_adapter_trade_count(); ++i) {
        uint64_t m, t, p, q;
        ME_adapter_trade_get(i, &m, &t, &p, &q);
        printf("%s%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64, i ? " " : "", m, t, p, q);
    }
    printf("]\n");
    return 0;
}
