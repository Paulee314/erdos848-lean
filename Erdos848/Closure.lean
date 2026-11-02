import Erdos848.Generated

set_option maxRecDepth 100000

namespace Erdos848

/-- The full 36-bit mask of all signatures. -/
def FULL : Nat := 2 ^ 36 - 1

/-- Signature index `i ↦ (a, b)` with `i = a * 9 + b`, `a ∈ Fin 4`, `b ∈ Fin 9`. -/
def sigA (i : Nat) : Nat := i / 9
def sigB (i : Nat) : Nat := i % 9

/-- Atom mask `R(i)` recomputed from the definition: bit `j` is set iff
    `4 ∣ aᵢ*aⱼ + 1` or `9 ∣ bᵢ*bⱼ + 1`. -/
def atomMask (i : Nat) : Nat :=
  (List.range 36).foldl (fun acc j =>
    if (sigA i * sigA j + 1) % 4 == 0 || (sigB i * sigB j + 1) % 9 == 0
    then acc + 2 ^ j else acc) 0

def atomsComputed : List Nat := (List.range 36).map atomMask

/-- The polar `R(X)`: intersect `R(i)` over the bits `i` set in `X`. -/
def polar (x : Nat) (atoms : List Nat) : Nat :=
  match atoms with
  | [] => FULL
  | m :: ms => (if x % 2 == 1 then m else FULL) &&& polar (x / 2) ms

/-- The generated atom masks agree with the definition. -/
theorem atoms_match : atomsR = atomsComputed := by decide

/-- There are exactly 64 Galois-closed signature sets. -/
theorem masks_count : closedMasks.length = 64 := by decide

/-- Every listed mask is Galois-closed: `R(R(X)) = X`. -/
theorem masks_closed :
    closedMasks.all (fun X => polar (polar X atomsR) atomsR == X) = true := by decide

/-- The listed masks are closed under pairwise intersection. -/
theorem masks_inter :
    closedMasks.all (fun X => closedMasks.all
      (fun Y => closedMasks.contains (X &&& Y))) = true := by decide

/-- There are exactly 439 valid pairs (the `opt_closure.py` enumeration). -/
theorem pairs_count : validPairs.length = 439 := by decide

/-- Every listed pair `(P, Q)` has both sides closed, satisfies `Q ⊆ R(P)`,
    and the script's validity condition (`R(P) ∩ R(Q) ≠ ∅`, or both polars
    nonempty). -/
theorem pairs_valid :
    validPairs.all (fun p =>
      closedMasks.contains p.1 && closedMasks.contains p.2 &&
      (p.2 &&& polar p.1 atomsR) == p.2 &&
      ((polar p.1 atomsR &&& polar p.2 atomsR) != 0 ||
       (polar p.1 atomsR != 0 && polar p.2 atomsR != 0))) = true := by decide

end Erdos848
