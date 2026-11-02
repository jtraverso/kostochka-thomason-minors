# Complete minors and average degree in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of the theorem of Kostochka (1982) and Thomason (1984): a graph
of average degree `d` has a complete minor of order `Ω(d / √(log d))`. The proof follows
N. Alon, M. Krivelevich and B. Sudakov, *Complete minors and average degree – a short proof*,
J. Graph Theory 103 (2023), 599–602 ([arXiv:2202.08530](https://arxiv.org/abs/2202.08530)).

| Lean | Statement |
|---|---|
| `KostochkaThomason.complete_minor_of_edges` | **AKS, Theorem 1.** There is `d₀` such that for every integer `d ≥ d₀`, every nonempty finite graph with at least `d · \|V\|` edges has a `K_t` minor for every `t ≤ d / (10 √(ln d))`. |
| `KostochkaThomason.kostochka_thomason` | **Kostochka–Thomason.** There is `c > 0` such that for every integer `d ≥ 2`, every nonempty finite graph with at least `d · \|V\|` edges has a `K_t` minor for every `t ≤ c · d / √(ln d)`. |

Minors are branch-set models (`CliqueMinors.MinorModel`, `CliqueMinors.IsMinor`), copied verbatim
from the registered entry PALOMAR-2026-10-16-000001
([jtraverso/hadwiger-mader](https://github.com/jtraverso/hadwiger-mader) @ `cb10154`), whose
library is a pinned dependency.

## The proof

- [`Reduce.lean`](KostochkaThomason/Reduce.lean): a minor-minimal graph with at least `d · |S|`
  edges has a vertex `x` of degree at most `2d` whose neighbours have at least `d` neighbours
  among the neighbours of `x` (contract edges in fewer than `d` triangles, delete surplus edges and
  isolated vertices).
- [`Robust.lean`](KostochkaThomason/Robust.lean): inside that neighbourhood, a piece in which every
  vertex has at least `2d/3` neighbours and which stays connected after removing fewer than `d/3`
  vertices.
- [`Connect.lean`](KostochkaThomason/Connect.lean): when every vertex has more than `|U|/6`
  neighbours, the diameter is at most `14`; a sample whose points have many sample neighbours has
  few components and becomes connected by adding short paths.
- [`Sampling.lean`](KostochkaThomason/Sampling.lean): Lemma 2 of AKS as a count over the `|U|^s`
  sequences of `s` vertices (Markov's inequality, a union bound and a Chernoff bound).
- [`Iterate.lean`](KostochkaThomason/Iterate.lean): the branch sets, one per step.
- [`Numeric.lean`](KostochkaThomason/Numeric.lean), [`Main.lean`](KostochkaThomason/Main.lean):
  the parameters (`s = ⌈3.2 √(ln d)⌉`, at most `12` components per sample) and the two theorems.

The details that differ from the article (sample size, `s/12` instead of `s/7`, explicit threshold)
are listed in [`formalization.yaml`](formalization.yaml).

## Checks

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

No `sorry`; both theorems depend only on `propext`, `Classical.choice` and `Quot.sound`; the
elaborated statements and definitions of `KostochkaThomasonChallenge` and
`KostochkaThomasonSolution` are identical.

The Lean development was written by Claude Opus 5.5 (Anthropic) under the author's direction (see
`formalization.yaml`). No independent human review of the formalization is claimed.
