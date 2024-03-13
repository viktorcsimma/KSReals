# Acorn
**An agda2hs-compatible, verifiable representation of exact-real arithmetic.**

## Purpose

The goal of this library is to create an Agda implementation of exact real arithmetic
described by Krebbers and Spitters in 2013.
The library discussed is based on their mathematical foundations
and the concepts of the [CoRN](https://github.com/coq-community/corn/) analysis library
(which has been written in Coq).
However, it takes a new approach on the topic,
and aims to popularise the field of verified exact-real arithmetic
by _first_ showing a runnable representation,
with most proofs filled in only after this has been achieved.
The goal of full compatibility with the [agda2hs](https://github.com/agda/agda2hs) compiler
makes the code not only much more efficient,
but also easier to understand and use.
The familiar, Haskell-style environment of Agda,
combined with CoRN's type class-based algebraic operators
would allow users of the library
to get started quickly with writing useful software
based on reliable calculations
proven to be correct.

## Compilation

Currently, Acorn is compatible with the version of agda2hs after PR #211 there.
After installing that, run this from the project root
to compile the sample program
(which calculates an approximation of _e_ with `1 / 10^{10^4)` precision):

```bash
agda2hs Main.agda && ghc Main.hs
```

## Contribution

Contributions are welcome!
Soon, I will provide a link to an article which functions as a documentation.