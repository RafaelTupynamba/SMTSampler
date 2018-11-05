# SMTSampler
SMTSampler: Efficient Stimulus Generation from Complex SMT Constraints

[Paper](https://people.eecs.berkeley.edu/~rtd/papers/SMTSampler.pdf)

# Building

Install dependencies

```
sudo apt install git g++ make python-minimal
```

Clone repos

```
git clone https://github.com/RafaelTupynamba/SMTSampler.git
git clone https://github.com/Z3Prover/z3.git
```

Build z3 (with a patch to compute the coverage of a formula)

```
cd z3
git checkout bf4edef761a9aaf1d303bde50b7bc768e6e018aa
cp ../SMTSampler/z3-patch/mk_util.py scripts/mk_util.py
cp ../SMTSampler/z3-patch/rewriter_def.h src/ast/rewriter/rewriter_def.h
cp ../SMTSampler/z3-patch/model.cpp src/model/model.cpp
python scripts/mk_make.py
cd build
make
sudo make install
cd ../..
```

Build SMTSampler

```
cd SMTSampler
make
```

# Running

Simply run with

```
./smtsampler -n 1000000 -t 3600.0 --smtbit formula.smt2
```

SMTSampler will create a file `formula.smt2.samples` with the samples generated and print statistics to standard output. The file `formula.smt2.samples` has one line for each produced sample. The first number represents the number of atomic mutations which were used to generate this sample. Then, the sample is displayed in a compact format.

The option -n can be used to specify the maximum number of samples produced and the option -t can be used to specify the maximum time allowed for sampling.

Three different strategies can be used for sampling, as described in the paper. With option `--smtbit`, we add one soft constraint for each bit inside a bit-vector. With option `--smtbv`, only one soft constraint is added for each bit-vector. Finally, option `--sat` encodes the SMT formula into SAT and performs the sampling over the converted SAT formula.

All the samples that SMTSampler outputs are valid solutions to the formula.

# Benchmarks

The benchmarks used come from SMT-LIB. They can be obtained from the following repositories.

[QF_AUFBV](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_AUFBV)
[QF_ABV](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_ABV)
[QF_BV](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_BV)

# Paper

[ICCAD 2018 paper](https://people.eecs.berkeley.edu/~rtd/papers/SMTSampler.pdf)

SMTSampler: Efficient Stimulus Generation from Complex SMT Constraints

Rafael Dutra, Jonathan Bachrach, Koushik Sen
