Gradual Effect Handlers
=======================

This project is a formalization of a language with effect handlers and
gradual types in Agda.  It consists of a core calculus with effect
handlers and explicit casts, and its metatheory.  This development is
written in Literate Agda; it can be read as a PDF document `doc.pdf`
included in the archive, which also illustrates the proof of gradual
guarantee with simulation diagrams.

This development was authored by

   [Li-yao Xia](https://poisson.chat/)
   [Philip Wadler](https://homepages.inf.ed.ac.uk/wadler/)

as part of the Huawei SAGE project at the University of Edinburgh.
It is based on code originally written by

   [Jeremy Siek](https://wphomes.soic.indiana.edu/jsiek/),
   [Peter Thiemann](http://www2.informatik.uni-freiburg.de/~thiemann/),
   and
   [Philip Wadler](https://homepages.inf.ed.ac.uk/wadler/).

[Link to the code repository](http://github.com/Lysxia/gradual-eff-paper)


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
- [standard-library 1.7.2](https://github.com/Agda/agda-stdlib)
- pandoc 2.19.2
- Python
- [pandoc-latex-environment](https://github.com/chdemko/pandoc-latex-environment)

Contents
--------

- the syntax of types and the imprecision relation (`Types.lagda.md`)
- the syntax of terms (intrinsically typed) (`Core.lagda.md`)
- an operational semantics, and an evaluator, which doubles as a proof of progress (`Progress.lagda.md`)
- the imprecision relation between terms (`Prec.lagda.md`)
- the proof of the gradual guarantee, as a simulation proof (`SimAux.lagda.md`, `Sim.lagda.md`)
- some example terms (`Example.lagda.md`, made more readable using an auxiliary module `Sugar.lagda.md`)
- general-purpose definitions (`Utils.lagda.md`, `VecPointwise2.lagda.md`)
