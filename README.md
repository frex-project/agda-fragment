# fragment
_FRex AGda augMENTation_

Requirements: Agda 2.6.1 and Standard Library 1.4

An extensible tactic for the Agda proof assistant, capable of synthesising proofs of algebraic identities. The tactic
(and its underlying formalisms) are all `--without-K --safe`, so it's compatible with a variety of Agda configurations
and, most importantly, constructive.

```agda
hello_world : ∀ {x y} → (2 + x) + (y + 3) ≡ x + (y + 5)
hello_world = fragment CSemigroupFrex +-csemigroup
```

The tactic builds on a library supporting the presentation of arbitrary finitary, mono-sorted (first-order)
equational-theories and can automatically derive specifications for solvers for their class of models
([_free extensions_](https://github.com/frex-project/agda-fragment/blob/main/src/Fragment/Equational/FreeExtension/Base.agda)).
The tactic is compatible with _any_ free extension making it very flexible: if you have an interesting algebraic structure,
you can write a solver and immediately leverage the tactic.

 At present, we have built-in support for:
- Semigroups
- Commutative semigroups
- ... (more to come) 

For some more examples, see [src/Fragment/Examples](https://github.com/frex-project/agda-fragment/blob/main/src/Fragment/Examples).

For a browsable overview of the interface, see the [API documentation](https://frex-project.github.io/agda-fragment/Everything.html).

For a full description see the following:

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Proof Synthesis with Free Extensions in Intensional Type Theory<br/>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Nathan Corbyn<br/>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Master's Thesis 2021<br/>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;[[bibtex](https://nathancorbyn.com/bib/proof_synthesis.bib)] [[pdf](https://nathancorbyn.com/pdf/proof_synthesis.pdf)]<br/>

It's also worth checking out the [other libraries](https://github.com/frex-project/) developed as part of the
[Frex Project](https://www.cl.cam.ac.uk/~jdy22/projects/frex/), and our publications.

[![Ubuntu build](https://github.com/frex-project/agda-fragment/actions/workflows/ci-ubuntu.yml/badge.svg)](https://github.com/frex-project/agda-fragment/actions/workflows/ci-ubuntu.yml)
