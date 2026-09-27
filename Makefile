CC ?= cc
CFLAGS ?= -O3 -Wall -Wextra -Werror -Ic/include

SRC_DIR = c/src
INC_DIR = c/include
BENCH_DIR = c/bench
TEST_DIR = c/tests
BIN_DIR = bin

SRCS = $(SRC_DIR)/matching_engine.c $(SRC_DIR)/matching_engine_gen.c

all: $(BIN_DIR)/bench_matching_engine $(BIN_DIR)/test_correctness

$(BIN_DIR):
	mkdir -p $(BIN_DIR)

$(BIN_DIR)/bench_matching_engine: $(BENCH_DIR)/bench_matching_engine.c $(SRCS) | $(BIN_DIR)
	$(CC) $(CFLAGS) -o $@ $< $(SRCS)

$(BIN_DIR)/test_correctness: $(TEST_DIR)/test_correctness.c $(SRCS) | $(BIN_DIR)
	$(CC) $(CFLAGS) -o $@ $< $(SRCS)

test: $(BIN_DIR)/test_correctness
	./$(BIN_DIR)/test_correctness

bench: $(BIN_DIR)/bench_matching_engine
	./$(BIN_DIR)/bench_matching_engine

verify:
	lake build

paper1:
	cd paper_formal_spec && pdflatex -interaction=nonstopmode paper.tex && pdflatex -interaction=nonstopmode paper.tex

paper2:
	cd paper_c_engine && pdflatex -interaction=nonstopmode paper.tex && pdflatex -interaction=nonstopmode paper.tex

all_papers: paper1 paper2

clean:
	rm -rf $(BIN_DIR) .lake

.PHONY: all test bench verify paper1 paper2 all_papers clean

# ---------------------------------------------------------------------------
# Generated matcher (plan v2 Phase 3): c/gen/matcher.c, printed from
# lean/Matcher/Program.lean, linked with the handwritten data layer through
# c/gen/engine_db_adapter.c. The handwritten engine supplies only
# MatchingEngine_CheckInvariants; its matcher entry points are renamed away.
GEN_DIR = c/gen
GEN_CFLAGS = $(CFLAGS) -I$(GEN_DIR)
HW_RENAME = -DMatchingEngine_Init=hw_MatchingEngine_Init \
            -DMatchingEngine_ProcessOrder=hw_MatchingEngine_ProcessOrder \
            -DMatchingEngine_CancelOrder=hw_MatchingEngine_CancelOrder
GEN_OBJS = $(BIN_DIR)/gen_matcher.o $(BIN_DIR)/gen_adapter.o $(BIN_DIR)/gen_glue.o \
           $(BIN_DIR)/gen_hw_engine.o $(BIN_DIR)/gen_data_layer.o

$(BIN_DIR)/gen_matcher.o: $(GEN_DIR)/matcher.c $(GEN_DIR)/engine_db.h | $(BIN_DIR)
	$(CC) $(GEN_CFLAGS) -std=c11 -c -o $@ $<
$(BIN_DIR)/gen_adapter.o: $(GEN_DIR)/engine_db_adapter.c $(GEN_DIR)/engine_db.h | $(BIN_DIR)
	$(CC) $(GEN_CFLAGS) -c -o $@ $<
$(BIN_DIR)/gen_glue.o: $(GEN_DIR)/matcher_glue.c | $(BIN_DIR)
	$(CC) $(GEN_CFLAGS) -c -o $@ $<
$(BIN_DIR)/gen_hw_engine.o: $(SRC_DIR)/matching_engine.c | $(BIN_DIR)
	$(CC) $(CFLAGS) $(HW_RENAME) -c -o $@ $<
$(BIN_DIR)/gen_data_layer.o: $(SRC_DIR)/matching_engine_gen.c | $(BIN_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

$(BIN_DIR)/test_correctness_gen: $(TEST_DIR)/test_correctness.c $(GEN_OBJS) | $(BIN_DIR)
	$(CC) $(GEN_CFLAGS) -o $@ $< $(GEN_OBJS)

test-gen: $(BIN_DIR)/test_correctness_gen
	./$(BIN_DIR)/test_correctness_gen

gen-matcher:
	./scripts/gen_matcher.sh

.PHONY: test-gen gen-matcher
