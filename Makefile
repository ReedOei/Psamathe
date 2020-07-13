KDISTR := $(HOME)/k-framework/k-distribution/bin
FLAGS :=

all: $(wildcard tests/exec/*.flow) $(wildcard tests/typecheck/*.flow)

common: flow-common.k flow-syntax.k
	$(KDISTR)/kompile --backend java flow-common.k

kompile: dynamic static

dynamic: dynamic/flow-kompiled/timestamp
static: static/flow-typecheck-kompiled/timestamp

dynamic/flow-kompiled/timestamp: flow.k flow-common.k flow-syntax.k
	$(KDISTR)/kompile --backend java flow.k -d dynamic/

static/flow-typecheck-kompiled/timestamp: flow-typecheck.k flow-common.k flow-syntax.k
	$(KDISTR)/kompile --backend java flow-typecheck.k -d static/

tests/exec/%.flow: kompile
	# $(KDISTR)/krun $(FLAGS) --directory static/ $@
	$(KDISTR)/krun $(FLAGS) --directory dynamic/ $@

tests/typecheck/%.flow: kompile
	$(KDISTR)/krun $(FLAGS) --directory static/ $@

clean:
	rm -rf dynamic/flow-kompiled
	rm -rf static/flow-typecheck-kompiled

