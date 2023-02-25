# Inductive Definition Transformers

[![Build status][action-badge]][action-link]

[action-badge]: https://github.com/ccyip/coq-idt/actions/workflows/build.yml/badge.svg?branch=master
[action-link]: https://github.com/ccyip/coq-idt/actions

This Coq library allows you to transform an inductive definition to another
inductive definition, by providing a *constructor transformer* tactic. It can be
used to generate boilerplate lemmas for backward and forward reasoning, and to
generate inductive types with many similar cases.

## Get Started

- [Abstract and talk at CoqPL 2022](https://popl22.sigplan.org/details/CoqPL-2022-papers/2/Scrap-your-boilerplate-definitions-in-10-lines-of-Ltac-)

- [Tutorial](/examples/tutorial.v)

## Installation

### Via Opam

``` sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-idt

```

### Dependencies

- [coq](https://coq.inria.fr) (8.14-8.16)
- [coq-metacoq-template](https://metacoq.github.io/) (>= 1.1)

## Gallery

A set of more complicated applications can be found in the Coq formalization of
[oblivious algebraic data types](https://github.com/ccyip/oadt/tree/idt).

- Generate lemmas about multi-parallel-reduction for backward reasoning:
  [theories/lang_oadt/mpared.v](https://github.com/ccyip/oadt/blob/idt/theories/lang_oadt/mpared.v)
- Generate inversion lemmas about the typing and kinding relations for forward
  reasoning:
  [theories/lang_oadt/inversion.v](https://github.com/ccyip/oadt/blob/idt/theories/lang_oadt/inversion.v)
- Generate the indistinguishability relation with mostly boring congruence
  cases:
  [theories/lang_oadt/indistinguishable.v](https://github.com/ccyip/oadt/blob/idt/theories/lang_oadt/indistinguishable.v)
- Generate an equivalent small-step semantics with the evaluation context rule
  (and the nonstandard "leaky" context rule) "expanded":
  [theories/lang_oadt/step_alt.v](https://github.com/ccyip/oadt/blob/idt/theories/lang_oadt/step_alt.v)
- Generate an equivalent intermediate semantics that admits a stronger induction
  principle:
  [theories/lang_oadt/reveal.v](https://github.com/ccyip/oadt/blob/idt/theories/lang_oadt/reveal.v)
