# CS550 Final Project

***TL;DR*** see `examples/gemv/sw/gemv*.scala` for implementation, reference, proof of gemv systolic array presented in paper.

## File organization

* `doc/` contains mostly copies of our previously submitted project documents, but some notes jotted down
* `examples/` each subfolder in here is a different systolic array. Within those subfolders we made a `sw` and `hw` folder for software and hardware respectively. For `gemm` there is only a (slightly modified) implementation file output from our DSL, while for `gemv` we have the hardware, Scala implementation, and stainless proof.
* `lib,project,src/`: all files belonging to the DSL and transpiler (called STAcomp). See below for instructions on running it.
    * `src/main/scala/stacomp/examples`: each of the scala files here is an example systolic array encoded in the DSL language.

## Makefile

The root of the repo has a makefile for running/verifying examples. `make` by default runs the DSL on the gemv example, then verifies the output with the provided proof on Stainless. Running `EXAMPLE=thing make` runs the class `stacomp.examples.thing` which is assumed to generate `examples/thing/sw/thingImpl.scala`, and it is subsequently verified with Stainless with `examples/thing/sw/thingRef.scala` and `examples/thing/sw/thingProof.scala` as input (assumed to be provided by the user). The only other example is `gemm`, which does not have a proof, so you can only use `EXAMPLE=gemm make compile`.