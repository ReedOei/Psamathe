KDISTR := $(HOME)/k-framework/k-distribution/bin
FLAGS :=
COMPILEFLAGS :=
# COMPILEFLAGS := --iterated -O3
BACKEND := haskell

all: kompile

pure-flow: $(wildcard tests/pure-flow/*.flow)

kompile: pure-flow-dynamic pure-flow-compiler

pure-flow-dynamic: pure-flow/pure-flow-kompiled/timestamp
pure-flow-compiler: pure-flow-compiler/pure-flow-compiler-kompiled/timestamp

pure-flow/pure-flow-kompiled/timestamp: pure-flow.k pure-flow-common.k
	$(KDISTR)/kompile $(COMPILEFLAGS) --backend $(BACKEND) pure-flow.k -d pure-flow/

pure-flow-compiler/pure-flow-compiler-kompiled/timestamp: pure-flow-compiler.k pure-flow-common.k
	$(KDISTR)/kompile $(COMPILEFLAGS) --backend $(BACKEND) pure-flow-compiler.k -d pure-flow-compiler/

tests/pure-flow/%.flow: pure-flow/pure-flow-kompiled/timestamp
	time ./flow pure test $(FLAGS) $@

tests/pure-flow-compiler/%.flow: pure-flow-compiler/pure-flow-compiler-kompiled/timestamp
	time ./flow pure-compile $(FLAGS) $@

clean:
	rm -rf pure-flow/pure-flow-kompiled
	rm -rf pure-flow-compiler/pure-flow-compiler-kompiled

