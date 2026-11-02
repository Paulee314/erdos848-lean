import Mathlib

namespace Erdos848

/-- A finite set `A` of natural numbers is *admissible* (Erdős Problem 848,
    diagonal convention) if `a * b + 1` is not squarefree for all `a, b ∈ A`,
    including `a = b`. -/
def IsAdmissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)

/-- Every element of `A` lies in the residue class `r` modulo 25. -/
def InClass25 (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ a ∈ A, a % 25 = r

/-- The type of `n`: its residue modulo `M = 900 = 4 * 9 * 25`. -/
def typeOf (n : ℕ) : ℕ := n % 900

/-- Two types `s, t` (residues mod 900) are *glued* if `4 ∣ s*t + 1`,
    `9 ∣ s*t + 1`, or `25 ∣ s*t + 1`. -/
def Glued (s t : ℕ) : Prop :=
  4 ∣ s * t + 1 ∨ 9 ∣ s * t + 1 ∨ 25 ∣ s * t + 1

end Erdos848
