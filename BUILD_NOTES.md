# Erdos848 Lean formalization — build notes

Project: formalize Claim #1 (the 1/50 stability theorem for Erdős #848) from
`stability_note/stability_note.tex` (Paulee314/erdos848).
Workflow (set 2026-11-02): **Muse (VM) writes all files and does the
reasoning; a Mac-side session runs the builds** and returns full logs.

## Build commands (Mac side)

```sh
cd /Users/paullee/Documents/antigravity/lucid-fermi/lean
lake exe cache get        # once: fetch Mathlib oleans for rev 54e71fa
lake build                # full build
grep -rn "sorry" Erdos848/ Erdos848.lean   # must be empty
```

Send back: the complete `lake build` output (or at minimum every error with
its file/line), plus the output of a file containing
`#print axioms Erdos848.max_le` once Maximization compiles.

Toolchain: `leanprover/lean4:v4.30.0-rc2` (pinned, matches Li's setup).
Rules: no `native_decide`, no `sorry`; finite checks by kernel `decide` over
`Nat`; main-theorem axioms must be exactly `[propext, Classical.choice,
Quot.sound]` (the `decide` theorems so far use only `[propext]`).

## Status (2026-11-02, Muse)

- `Erdos848/Generated.lean` — data generated from `stability/opt_closure.py`
  and recomputed independently in Python: 64 closed masks, 439 valid pairs,
  36 atom masks. Hashes in the file header.
- `Erdos848/Closure.lean` — atom/polar definitions; `atoms_match`,
  `masks_count`, `masks_closed`, `masks_inter`, `pairs_count`, `pairs_valid`,
  all `by decide`. **Pre-verified by Muse in core Lean v4.30.0-rc2 (no
  Mathlib) before delivery** — see SmokeTest result in the prep folder.
  Needs `set_option maxRecDepth 100000` (kernel decide depth).
- `Erdos848/Maximization.lean` — pinned scaled constants and the `F9`
  maximization over the 439 pairs, `by decide` (same pre-verification).
- `Erdos848/Basic.lean` — definitions only so far (`IsAdmissible` via
  Mathlib `Squarefree`, `InClass25`, `typeOf`, `Glued`). Not yet compiled
  against Mathlib — first Mac build tests it. Theorem statements are NOT
  stubbed with `sorry`; they get added only with proofs.

## Pinned constants (exact rational arithmetic, Python `Fraction`)

Union-bound route (primality-free), `T = 10^4`:

- `k = Σ_{q≥7} q⁻² ≤ 1/49 + Σ_{11≤n≤10⁴, gcd(n,210)=1} n⁻² + 1/T`
  `= 0.0517582487…` (true value 0.0511359…), so `Ks = 51759`.
- `d = Σ_{p∈𝒟} p⁻² ≤ (exact sum over primes ≤ 10⁴) + 1/(16·2499)`
  `= 0.0138339054…` (true 0.0138136…).
- `j = d·(1 + 2k) ≤ 0.0152659428…` (paper's product-based `J' = 0.0142450`),
  so `Js = 15266`.
- Binding check: `72·Ks + 828·Js = 16,366,896 < 18,000,000`. Margin 1,633,104.
  (The paper's product constants give 15,403,040-ish; an earlier task spec
  quoted ~16.97×10⁶, which matches neither route — superseded by the above.)

## Two warnings

1. **Pair-set parametrization.** `validPairs` is `opt_closure.py`'s
   enumeration: `(P, Q)` closed with `Q ⊆ R(P)` plus the script's validity
   condition. The paper Lemma 6.1 instead phrases pairs as `(A, B)` with
   `R(A) ⊆ B`. Both sets have 439 elements but intersect in only 62 pairs.
   The maximization `F` belongs to the script's parametrization (it is the
   one cross-validated against the direct 900-type definition and 3000
   random configurations). Formalize the script's version; do not
   "correct" the pairs from the lemma text.
2. **Open spec gaps (from Muse's 2026-11-02 audit).**
   - The explicit target `50·|A| ≤ N + 50·(2700·π(N) + C)` is not in the
     paper and is not proved as stated: the truncation lemma's CRT error is
     `O_T(1)` per type, not an absolute constant `C`. A corrected explicit
     statement has to be derived before `SieveAssembly.lean` has a target.
   - `π(N) = o(N)` is the Prime Number Theorem — a Mathlib library citation
     (real analysis), not an elementary `decide` lemma. The paper's explicit
     route uses Rosser's bound `π(x) < 1.25506·x/log x` instead.
   - `WheelBounds.lean` / `SieveAssembly.lean` (CRT counting, per-type
     assembly) are new analytic proof work, not transcription: the paper's
     Prop. (per-type bound) runs through Euler products and limits.

## Next steps queue

1. Mac build of the current four files; fix `Basic.lean` Mathlib issues.
2. `LocalFacts.lean`: F1–F3 factored over `Fin 4`, `Fin 9`, `Fin 25`.
3. Lemma 6.1 completeness (every Galois-closed set is in `closedMasks`):
   short induction from `masks_inter` + atoms — real proof, not `decide`.
4. Derive the corrected explicit per-type bound; then WheelBounds and
   SieveAssembly.
