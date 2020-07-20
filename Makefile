KDISTR := $(HOME)/k-framework/k-distribution/bin
FLAGS :=
BACKEND := haskell

all: exec typecheck

exec: $(wildcard tests/exec/*.flow)

typecheck: $(wildcard tests/typecheck/*.flow)

common: flow-common.k flow-syntax.k
	$(KDISTR)/kompile --backend $(BACKEND) flow-common.k

kompile: dynamic static

dynamic: dynamic/flow-kompiled/timestamp
static: static/flow-typecheck-kompiled/timestamp

dynamic/flow-kompiled/timestamp: flow.k flow-common.k flow-syntax.k
	$(KDISTR)/kompile --backend $(BACKEND) flow.k -d dynamic/

static/flow-typecheck-kompiled/timestamp: flow-typecheck.k flow-common.k flow-syntax.k
	$(KDISTR)/kompile --backend $(BACKEND) flow-typecheck.k -d static/

tests/exec/%.flow: dynamic/flow-kompiled/timestamp static/flow-typecheck-kompiled/timestamp
	time ./flow test $(FLAGS) $@

tests/typecheck/%.flow: static/flow-typecheck-kompiled/timestamp
	time ./flow typecheck $(FLAGS) $@

clean:
	rm -rf dynamic/flow-kompiled
	rm -rf static/flow-typecheck-kompiled

