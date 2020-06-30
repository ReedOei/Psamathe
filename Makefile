KDISTR := $(HOME)/k-framework/k-distribution/bin

all: $(wildcard tests/*.flow)

kompile: dynamic/flow-kompiled/timestamp static/flow-typecheck-kompiled/timestamp

dynamic/flow-kompiled/timestamp: flow.k
	$(KDISTR)/kompile --backend java flow.k -d dynamic/

static/flow-typecheck-kompiled/timestamp: flow-typecheck.k
	$(KDISTR)/kompile --backend java flow-typecheck.k -d static/

%.flow: kompile
	krun --directory static/ --verbose $@
	# krun --directory dynamic/ --verbose $@.out

clean:
	rm -rf dynamic/flow-kompiled
	rm -rf static/flow-typecheck-kompiled

