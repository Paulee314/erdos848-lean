import Erdos848.Closure

set_option maxRecDepth 100000

namespace Erdos848

/-- Number of set bits among the low 36 bits. -/
def pop36 (x : Nat) : Nat := (List.range 36).countP (fun i => x.testBit i)

/-- Pinned scaled constants (derivation in BUILD_NOTES.md):
    `Ks = ⌈10^6 · k_bound⌉`, `Js = ⌈10^6 · j_bound⌉` for the union-bound caps
    `k_bound = 0.0517582487…` and `j_bound = 0.0152659428…`. -/
def Ks : Nat := 51759
def Js : Nat := 15266

/-- `F9(P, Q) = 900 · 10^6 · F(P, Q)` with `K₂'`, `J'` replaced by the scaled
    union-bound caps `Ks / 10^6`, `Js / 10^6`, where
    `F(P, Q) = (1-K)(|P|+|Q|) + K(|R(P)|+|R(Q)|) + 23·J·|R(P) ∩ R(Q)|` all
    divided by 900. Integer arithmetic only. -/
def F9 (P Q : Nat) : Nat :=
  (1000000 - Ks) * (pop36 P + pop36 Q)
  + Ks * (pop36 (polar P atomsR) + pop36 (polar Q atomsR))
  + 23 * Js * pop36 (polar P atomsR &&& polar Q atomsR)

/-- The computational heart of Theorem 6.2 (opt): over all 439 valid pairs,
    `F ≤ 18/900 = 1/50`, in scaled form `F9 ≤ 18 · 10^6`. -/
theorem max_le : validPairs.all (fun p => F9 p.1 p.2 <= 18000000) = true := by decide

/-- The bound is attained by exactly two pairs (the `{7,93}` and `{43,57}`
    configurations). -/
theorem max_attained : validPairs.countP (fun p => F9 p.1 p.2 == 18000000) = 2 := by decide

/-- The runner-up value `72·Ks + 828·Js = 16,366,896` (the all-types
    configuration) occurs exactly once. -/
theorem runner_up_present :
    validPairs.countP (fun p => F9 p.1 p.2 == 16366896) = 1 := by decide

end Erdos848
