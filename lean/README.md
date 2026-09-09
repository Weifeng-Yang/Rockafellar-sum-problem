# Nonmaximal sums of maximally monotone operators

## Introduction

We construct counterexamples to Rockafellar's sum conjecture on $c_0$ and standard $\ell^1$: two maximally monotone operators satisfy the interior-domain condition, and their sum is not maximally monotone. In each example, one summand is a bounded positive rank-one operator defined on the whole space. We establish a general construction theorem that characterizes maximality and identifies when such a perturbation produces a nonmaximal sum. The construction on $c_0$ couples triangular operators with a Lipschitz curve, and a bounded surjection transfers the construction to standard $\ell^1$.

This package contains Lean proofs for the counterexample on $c_0$ and the general pullback lemma in the paper [1]. The paper's general construction theorem and concrete counterexample on standard $\ell^1$ are not formalized in this package.

## Lean code

- [BlockMassCounterexample.lean](BlockMassCounterexample.lean) assembles the counterexample on $c_0$ and proves maximality of both operators, the interior-domain condition, and nonmaximality of their sum.
- [BlockMassPullback.lean](BlockMassPullback.lean) proves the general pullback lemma.
- [Audit.lean](Audit.lean) prints theorem statements and their axiom dependencies.

## How to run our code

Install Lean through [elan](https://github.com/leanprover/elan), then run the following commands from this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The included configuration selects Lean 4.19.0 and pins the mathlib dependencies. The first run requires network access to download dependencies.

## Reference

[1] Weifeng Yang. *Nonmaximal sums of maximally monotone operators under Rockafellar's constraint qualification*.
