# Lazy Decision Procedure for WSkS

### Formula File Syntax

Input WS2S formula is specified according to the following syntax. It is a
subset of syntax MONA extended by additional atomic predicates.

```
file ::= (header;) (formula; | decl*)

header ::= ws2s

decl ::= pred var (params)* = formula;

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
    | var = var.0
    | var = var.1

const ::= root(.(0+1))*
```

Note that for experimental purposes it is possible to use full MONA syntax,
however, it requires local installation of MONA tool and enabling the option
*useMona* in *src/Main.hs*.

### Haskell Package Dependencies

* mtl
* time
* parsec
* temporary
* process

You can install the packages via
```
$ cabal install <package>
```
