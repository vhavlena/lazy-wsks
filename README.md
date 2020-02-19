# AntiMona & Lazy Decision Procedure for WS2S

[![Build Status](https://travis-ci.org/vhavlena/lazy-wsks.svg?branch=master)](https://travis-ci.org/vhavlena/lazy-wsks)

This repository contains the AntiMona (Antiprenexing for Mona) prototype tool
for static formula transformations (antiprenexing & stuff) and the LazyWSkS
prototype tool implementing lazy decision procedure for WS2S.

### Install

For a successful run of the tools and all their features *python3*, *ghc* of
version 8.4 or greater, and *cabal* of version 2.2 or greater is needed. To compile
the tools carry out the following steps:

1. Install required Haskell and Python packages (below)
2. Run ``` $ make release ``` in the root folder (for *LazyWSkS*) or
3. Run ``` $ make antiprenex-release ``` in the root folder (for *AntiMona*)

The tests for the LazyWSkS can be run via ``` $ make test ``` .


#### Haskell Package Dependencies

* mtl
* time
* parsec
* temporary
* process
* bimap
* split
* strict-io
* network

You can install the packages via
```
$ cabal install <package>
```
or just
```
$ make install
```

#### Python Package Dependencies

Python scripts are used only for testing and automatized experimental
evaluation.

* termcolor

You can install the packages via
```
$ pip install <package>
```

#### AntiMona Specific Dependencies

For a successful run of the tool, the extended version of Mona is necessary. The
extension provides further statistics about input formulae. This extended
version you can download and install from
[https://github.com/Iorethan/predict_mona](https://github.com/Iorethan/predict_mona).

---

## AntiMona

The tool AntiMona is a prototype tool implementing static formula
transformations (antiprenexing). The tool reads a file in Mona format and
applies transformations on it. The output is written in Mona format. The input
format allows to specify WS1S and WS2S formulae (specifications involving WSRT
are not supported).

Before running of the tool you need to launch (from ``` external ``` directory)
```
$ ./predict.py <path to predict mona>
```
This script serves as a server and AntiMona communicates with it, so it must be
running during the time of AntiMona preprocessing.

To preprocess a Mona file run
```
$ ./AntiMona <file>
```
This command flattens the input formula followed by the transformations. To
transform a formula on a level of predicates run
```
$ ./AntiMona <file> -p
```

---

## Lazy Decision Procedure for WS2S

### Formula File Syntax

Input *ground* WS2S formula is specified according to the following syntax. It is a
subset of syntax MONA extended by additional atomic predicates.

```
file ::= (header;) (formula; | decl*)

header ::= ws2s

decl ::= pred var ( params* ) = formula;

formula ::= true
    | false
    | (formula)
    | ~formula
    | formula | formula
    | formula & formula
    | formula => formula
    | formula <=> formula
    | first-order-term
    | second-order-term
    | ex1 (var)+ : formula
    | ex2 (var)+ : formula
    | all1 (var)+ : formula
    | all2 (var)+ : formula

first-order-term ::= var = const

second-order-term ::= var = var
    | var ~= var
    | var sub var
    | sing var
    | eps var
    | var in var
    | var = var.0
    | var = var.1

const ::= root(.(0+1))*
```

Note that for experimental purposes it is possible to use full MONA syntax,
however, it requires local installation of MONA tool and enabling the option
*useMona* in *src/Main.hs*.

#### Example
```
pred allsub (var2 X) = all2 Y: X sub Y;
all2 X: ex1 x: (x in X | allsub(X));
```
