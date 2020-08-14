KDISTR := $(HOME)/k-framework/k-distribution/bin
FLAGS :=
COMPILEFLAGS :=
# COMPILEFLAGS := --iterated -O3
BACKEND := haskell

all: exec typecheck compile pure-flow

exec: $(wildcard tests/exec/*.flow)
typecheck: $(wildcard tests/typecheck/*.flow)
compile: $(wildcard tests/compile/*.flow)
pure-flow: $(wildcard tests/pure-flow/*.flow)

common: flow-common.k flow-syntax.k
	$(KDISTR)/kompile --backend $(BACKEND) flow-common.k

kompile: dynamic static compiler pure-flow-dynamic

dynamic: dynamic/flow-kompiled/timestamp
static: static/flow-typecheck-kompiled/timestamp
compiler: compiler/flow-compiler-kompiled/timestamp
pure-flow-dynamic: pure-flow/pure-flow-kompiled/timestamp

compiler/flow-compiler-kompiled/timestamp: flow-compiler.k yul-syntax.k flow-common.k flow-syntax.k
	$(KDISTR)/kompile --hook-namespaces KRYPTO $(COMPILEFLAGS) --backend $(BACKEND) flow-compiler.k -d compiler/

dynamic/flow-kompiled/timestamp: flow.k flow-common.k flow-syntax.k
	$(KDISTR)/kompile $(COMPILEFLAGS) --backend $(BACKEND) flow.k -d dynamic/

static/flow-typecheck-kompiled/timestamp: flow-typecheck.k flow-common.k flow-syntax.k
	$(KDISTR)/kompile $(COMPILEFLAGS) --backend $(BACKEND) flow-typecheck.k -d static/

pure-flow/pure-flow-kompiled/timestamp: pure-flow.k
	$(KDISTR)/kompile $(COMPILEFLAGS) --backend $(BACKEND) pure-flow.k -d pure-flow/

tests/exec/%.flow: dynamic/flow-kompiled/timestamp static/flow-typecheck-kompiled/timestamp
	time ./flow test $(FLAGS) $@

tests/typecheck/%.flow: static/flow-typecheck-kompiled/timestamp
	time ./flow typecheck test $(FLAGS) $@

tests/compile/%.flow: compiler/flow-compiler-kompiled/timestamp
	time ./flow compile test $(FLAGS) $@

tests/pure-flow/%.flow: pure-flow/pure-flow-kompiled/timestamp
	time ./flow pure test $(FLAGS) $@

clean:
	rm -rf dynamic/flow-kompiled
	rm -rf static/flow-typecheck-kompiled
	rm -rf compiler/flow-compiler-kompiled
	rm -rf pure-flow/pure-flow-kompiled

