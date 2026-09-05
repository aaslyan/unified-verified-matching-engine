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
