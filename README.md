Gradual Effect Handlers
=======================

This project is a formalization of a language with effect handlers and gradual types in Agda.
It consists of a core calculus with effect handlers and explicit casts, and its metatheory.
This development is written in Literate Agda;
it can be read as a PDF document `doc.pdf` included in the archive,
which also illustrates the proof of gradual guarantee with simulation diagrams.

Build
-----

The definitions and proofs can be checked with the following command (it takes a couple of minutes):

```
make check
```

The PDF document can be (re)compiled with:

```
make doc
```

The main dependencies are (latest versions as of May 2023):

- Agda 2.6.3
- standard-library 1.7.2
- pandoc 2.19.2

Contents
--------

- the syntax of types and the imprecision relation (`Types.lagda.md`)
- the syntax of terms (intrinsically typed) (`Core.lagda.md`)
- an operational semantics, and an evaluator, which doubles as a proof of progress (`Progress.lagda.md`)
- the imprecision relation between terms (`Prec.lagda.md`)
- the proof of the gradual guarantee, as a simulation proof (`SimAux.lagda.md`, `Sim.lagda.md`)
- some example terms (`Example.lagda.md`, made more readable using an auxiliary module `Sugar.lagda.md`)
- general-purpose definitions (`Utils.lagda.md`, `VecPointwise2.lagda.md`)
