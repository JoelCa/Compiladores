Tiger Compiler
============

Tiger Compiler for ARMv7.

It's based in the book "Modern Compiler Implementation in ML".

## Setup

Download the code from the `entrega3` folder.
Then, do the `make` command.

## Use

You can generate the arm assembler from a tiger file:

```
$ ./tiger_compiler.sh <tiger file>
```

## Tests

The test examples are in `test` folder.

If you are in the `entrega3` folder, you can get the assembler of
`merge.tig` as follows:

```
$ ./tiger_compiler.sh ../tests/good/merge.tig
```
