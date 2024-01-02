EXAMPLE ?= gemv

exampleDir = examples/$(EXAMPLE)/

all: verify


verify: $(exampleDir)/sw/$(EXAMPLE)Impl.scala $(exampleDir)/sw/$(EXAMPLE)Proof.scala
	stainless $^

compile: $(exampleDir)/sw/$(EXAMPLE)Impl.scala
$(exampleDir)/sw/$(EXAMPLE)Impl.scala: src/main/scala/stacomp/examples/$(EXAMPLE).scala $(exampleDir)/sw
	sbt "runMain stacomp.examples.$(EXAMPLE) compile $@"

$(exampleDir)/sw:
	mkdir -p $@
#synth: $(EXAMPLE)/gen/$(EXAMPLE)Gen.v
#$(EXAMPLE)/gen/$(EXAMPLE)Gen.v: $(EXAMPLE)/$(EXAMPLE).scala
#    scala-cli $@ -- $


#import argparse
#import subprocess
#import sys
#
#if __name__ == "__main__":
#    parser = argparse.ArgumentParser()
#    parser.add_argument("example")
#    parser.add_argument("mode", choices=["verify", "synth"])
#
#    args = parser.parse_args()
#
#    if args.mode == "verify":
#        subprocess.run(["stainless", f"{args.example}/{args.example}.scala", f"{args.example}/{args.example}Proof.scala"])
#    else:
#        print("Unimplemented")
#        sys.exit(-1)

