KDISTR := $(HOME)/k-framework/k-distribution/bin

all: $(wildcard tests/*.flow)

kompile: flow-kompiled/timestamp
	$(KDISTR)/kompile --backend java flow.k

%.flow: kompile
	krun --verbose $@

