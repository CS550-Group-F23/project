EXAMPLE ?= gemv

exampleDir = examples/$(EXAMPLE)/

all: verify

verify: $(exampleDir)/sw/$(EXAMPLE)Impl.scala $(exampleDir)/sw/$(EXAMPLE)Ref.scala $(exampleDir)/sw/$(EXAMPLE)Proof.scala
	stainless $^

compile: $(exampleDir)/sw/$(EXAMPLE)Impl.scala
$(exampleDir)/sw/$(EXAMPLE)Impl.scala: src/main/scala/stacomp/examples/$(EXAMPLE).scala $(exampleDir)/sw
	sbt "runMain stacomp.examples.$(EXAMPLE) compile $@"

$(exampleDir)/sw:
	mkdir -p $@
#synth: $(EXAMPLE)/gen/$(EXAMPLE)Gen.v
#$(EXAMPLE)/gen/$(EXAMPLE)Gen.v: $(EXAMPLE)/$(EXAMPLE).scala
#    scala-cli $@ -- $
