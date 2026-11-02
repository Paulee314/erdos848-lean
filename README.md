# erdos848-lean

Lean 4 formalization of the **1/50 stability theorem for Erdős Problem #848**,
in progress.

## Attribution

Erdős Problem #848 itself was proved for all N by **A. C. Li**
([crabsatellite/erdos-848-squarefree-product](https://github.com/crabsatellite/erdos-848-squarefree-product)).
This repository does **not** formalize Li's proof. It formalizes the stability
refinement from the accompanying note — see
[Paulee314/erdos848](https://github.com/Paulee314/erdos848) (the paper,
verification bundle, and certificates; DOI
[10.5281/zenodo.23874488](https://doi.org/10.5281/zenodo.23874488)).

## Status

Verified (kernel-checked; no `sorry`, no `native_decide`; axioms within
`[propext, Classical.choice, Quot.sound]`, several finite theorems using only
`[propext]` or no axioms):

- `Erdos848/Closure.lean`, `Erdos848/Maximization.lean` — the finite core:
  the 64 Galois-closed type sets mod 900, closure under intersection, and the
  maximization over the 439 valid pairs. The scaled objective is at most
  18,000,000 (the 1/50 density bound), attained exactly by the two extremal
  configurations {7, 93} and {43, 57} mod 100, with the runner-up pinned at
  16,366,896.
- `Erdos848/LocalFacts.lean` — F1 complete: the finite checks mod 4/9/25,
  Euler's criterion (no prime p ≡ 3 (mod 4) divides n² + 1), and the Hensel
  root bound (at most two roots of x² ≡ −1 mod p and mod p²). Plus F3,
  factored through mod 25, and the classification of exactly two mixed
  mod-100 class pairs, (7, 93) and (57, 43). Plus the bridge
  (`Glued s t ↔ gluedB s t = true`, identifying the Bool checks with the
  Prop predicate) and the F2 transfer (`Glued a b ↔ Glued (typeOf a)
  (typeOf b)`: gluing of integers depends only on their types mod 900).

In progress / queued:

- Bridge lemmas identifying the Bool checks with the `Glued` predicate, and
  the F2 transfer (gluing of integers depends only on their types mod 900).
- Lemma 6.1 completeness (every Galois-closed set is among the 64).
- The sieve assembly and the main theorem. See `BUILD_NOTES.md` for the
  pinned constants and the known gaps between the original task spec and
  the paper.

## Build

Toolchain pinned by `lean-toolchain` (Lean 4.30.0-rc2; Mathlib at the rev in
`lake-manifest.json`):

```sh
lake exe cache get
lake build
```

## License

CC BY 4.0 (see `LICENSE`).
