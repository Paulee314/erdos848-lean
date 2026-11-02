import Erdos848.Basic

set_option maxRecDepth 100000

namespace Erdos848

/-- Decidable (Bool) form of `Glued` for residues: `4 ∣ s*t + 1`, `9 ∣ s*t + 1`,
    or `25 ∣ s*t + 1`, tested by remainders. The finite theorems in this file
    are proved by kernel `decide` and were pre-verified in core Lean before
    delivery; `f1_prime_three_mod_four` is the file's first Mathlib-tier
    proof. The bridge `Glued s t ↔ gluedB s t = true` on residues, and the
    F2 transfer (gluing of integers depends only on their types mod 900),
    remain queued. -/
def gluedB (s t : ℕ) : Bool :=
  (s * t + 1) % 4 == 0 || (s * t + 1) % 9 == 0 || (s * t + 1) % 25 == 0

/-- Bool form of "type lies in an extremal class mod 25". -/
def inCB (s : ℕ) : Bool := s % 25 == 7 || s % 25 == 18

/-! ## F1, finite parts, and the two genuine theorems

Two parts of F1 are genuine theorems rather than finite checks, both
proved below for every prime `p` (the paper needs them for `p ∈ 𝒟`): no
prime `p ≡ 3 (mod 4)` divides `n^2 + 1` (Euler's criterion), and
`x^2 ≡ -1` has at most two roots modulo `p` and modulo `p^2` (the Hensel
root bound, by lift uniqueness). The referee's `local_facts.py` checks
those only for `p < 2000` / `p < 400`. -/

/-- F1: `n^2 + 1` is never divisible by 4. -/
theorem f1_mod4 : (List.range 4).all (fun n => (n * n + 1) % 4 != 0) = true := by
  decide

/-- F1: `n^2 + 1` is never divisible by 9. -/
theorem f1_mod9 : (List.range 9).all (fun n => (n * n + 1) % 9 != 0) = true := by
  decide

/-- F1: the roots of `n^2 + 1 ≡ 0 (mod 25)` are exactly `7` and `18`. -/
theorem f1_mod25_roots :
    (List.range 25).filter (fun n => (n * n + 1) % 25 == 0) = [7, 18] := by
  decide

/-- F1, Euler part: no prime `p ≡ 3 (mod 4)` divides `n^2 + 1`, since in
    `ZMod p` that would make `-1` a square. Depends only on the standard
    axioms `[propext, Classical.choice, Quot.sound]` (via Mathlib's
    `ZMod.mod_four_ne_three_of_sq_eq_neg_one`). -/
theorem f1_prime_three_mod_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (n : ℕ) :
    ¬ p ∣ n * n + 1 := by
  intro hd
  have hcast : ((n * n + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hd
  have h : (n : ZMod p) ^ 2 = -1 := by
    push_cast at hcast
    rw [pow_two]
    exact eq_neg_of_add_eq_zero_left hcast
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one h hp

/-! ## F1, root counts: at most two roots mod `p` and mod `p^2` -/

open Polynomial in
/-- Roots of `x^2 = -1` in `ZMod p` number at most 2 (polynomial root bound). -/
theorem roots_mod_p_card_le (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter (fun a : ZMod p => a ^ 2 = -1)).card ≤ 2 := by
  have hpoly : (X ^ 2 + 1 : (ZMod p)[X]) ≠ 0 := by
    have hmonic : (X ^ 2 + 1 : (ZMod p)[X]).Monic := by
      have h1 : (1 : (ZMod p)[X]) = C 1 := (C_1).symm
      rw [h1]
      exact monic_X_pow_add_C 1 (by norm_num : (2 : ℕ) ≠ 0)
    exact hmonic.ne_zero
  have hdeg : (X ^ 2 + 1 : (ZMod p)[X]).natDegree = 2 := by compute_degree!
  have hcard := Polynomial.card_roots' (X ^ 2 + 1 : (ZMod p)[X])
  rw [hdeg] at hcard
  have hset : Finset.univ.filter (fun a : ZMod p => a ^ 2 = -1)
      = (X ^ 2 + 1 : (ZMod p)[X]).roots.toFinset := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      Polynomial.mem_roots hpoly, Polynomial.IsRoot.def, eval_add, eval_pow, eval_X,
      eval_one]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  rw [hset]
  exact (Multiset.toFinset_card_le _).trans hcard

open Polynomial in
/-- Roots of `x^2 = -1` in `ZMod (p^2)` number at most 2: the reduction map
    to `ZMod p` is injective on roots (elementary Hensel lift uniqueness). -/
theorem roots_mod_p2_card_le (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter (fun x : ZMod (p ^ 2) => x ^ 2 = -1)).card ≤ 2 := by
  have hp : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst hp2
    have hsub : Finset.univ.filter (fun x : ZMod (2 ^ 2) => x ^ 2 = -1)
        ⊆ {(1 : ZMod (2 ^ 2)), 3} := by
      intro x hx
      have hx2 : x ^ 2 = -1 := (Finset.mem_filter.1 hx).2
      have hval : x.val = 1 ∨ x.val = 3 := by
        have hlt4 : x.val < 4 := ZMod.val_lt x
        have hd : (2 : ℕ) ^ 2 ∣ x.val ^ 2 + 1 := by
          have hcast : ((x.val ^ 2 + 1 : ℕ) : ZMod (2 ^ 2)) = 0 := by
            rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val, hx2]
            exact neg_add_cancel _
          exact (ZMod.natCast_eq_zero_iff _ _).1 hcast
        obtain ⟨k, hk⟩ := hd
        interval_cases x.val <;> norm_num at hk ⊢ <;> omega
      have hxeq : ∀ v : ℕ, x.val = v → x = (v : ZMod (2 ^ 2)) := fun v hv => by
        rw [← ZMod.natCast_zmod_val x, hv]
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hval with h | h
      · left; rw [hxeq 1 h]; norm_num
      · right; rw [hxeq 3 h]; norm_num
    have hcard : ({(1 : ZMod (2 ^ 2)), 3} : Finset (ZMod (2 ^ 2))).card ≤ 2 := by
      refine (Finset.card_insert_le _ _).trans ?_
      simp
    exact (Finset.card_le_card hsub).trans hcard
  · haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
    set φ : ZMod (p ^ 2) →+* ZMod p :=
      ZMod.castHom (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)) (ZMod p) with hφdef
    have hmaps : Set.MapsTo φ ↑(Finset.univ.filter (fun x : ZMod (p ^ 2) => x ^ 2 = -1))
        ↑(Finset.univ.filter (fun a : ZMod p => a ^ 2 = -1)) := by
      intro x hx
      have hx2 : x ^ 2 = -1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
      have h2 : φ x ^ 2 = -1 := by
        rw [← map_pow, hx2]
        simp
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩)
    have hinj : Set.InjOn φ ↑(Finset.univ.filter (fun x : ZMod (p ^ 2) => x ^ 2 = -1)) := by
      intro x hx y hy hxy
      have hx2 : x ^ 2 = -1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
      have hy2 : y ^ 2 = -1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
      have hda : p ^ 2 ∣ x.val ^ 2 + 1 := by
        have hcast : ((x.val ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 := by
          rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val, hx2]
          exact neg_add_cancel _
        exact (ZMod.natCast_eq_zero_iff _ _).1 hcast
      have hdb : p ^ 2 ∣ y.val ^ 2 + 1 := by
        have hcast : ((y.val ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 := by
          rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val, hy2]
          exact neg_add_cancel _
        exact (ZMod.natCast_eq_zero_iff _ _).1 hcast
      have hmodp : (x.val : ZMod p) = (y.val : ZMod p) := by
        have e1 : φ x = (x.val : ZMod p) := by
          conv_lhs => rw [← ZMod.natCast_zmod_val x]
          exact map_natCast φ x.val
        have e2 : φ y = (y.val : ZMod p) := by
          conv_lhs => rw [← ZMod.natCast_zmod_val y]
          exact map_natCast φ y.val
        rw [e1, e2] at hxy
        exact hxy
      have hpdiff : (p : ℤ) ∣ (x.val : ℤ) - (y.val : ℤ) := by
        have h0 : (((x.val : ℤ) - (y.val : ℤ) : ℤ) : ZMod p) = 0 := by
          have hsub : (x.val : ZMod p) - (y.val : ZMod p) = 0 := by
            rw [hmodp]; exact sub_self _
          push_cast
          exact hsub
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0
      have hdaZ : (p : ℤ) ^ 2 ∣ (x.val : ℤ) ^ 2 + 1 := by exact_mod_cast hda
      have hdbZ : (p : ℤ) ^ 2 ∣ (y.val : ℤ) ^ 2 + 1 := by exact_mod_cast hdb
      have hprod : (p : ℤ) ^ 2 ∣ ((x.val : ℤ) - (y.val : ℤ)) * ((x.val : ℤ) + (y.val : ℤ)) := by
        have hsub : (p : ℤ) ^ 2 ∣ ((x.val : ℤ) ^ 2 + 1) - ((y.val : ℤ) ^ 2 + 1) :=
          dvd_sub hdaZ hdbZ
        convert hsub using 1 <;> ring
      have hpdiff' := hpdiff
      obtain ⟨s, hs⟩ := hpdiff
      have hp0Z : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
      have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.2 (by simpa using hp)
      have hps : (p : ℤ) ∣ s * ((x.val : ℤ) + (y.val : ℤ)) := by
        have e : (p : ℤ) * (s * ((x.val : ℤ) + (y.val : ℤ)))
            = ((x.val : ℤ) - (y.val : ℤ)) * ((x.val : ℤ) + (y.val : ℤ)) := by
          rw [hs]; ring
        have h1 : (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * (s * ((x.val : ℤ) + (y.val : ℤ))) := by
          rw [e]
          exact pow_two (p : ℤ) ▸ hprod
        exact (Int.mul_dvd_mul_iff_left hp0Z).1 h1
      have hnsum : ¬ (p : ℤ) ∣ (x.val : ℤ) + (y.val : ℤ) := by
        intro hsum
        have h2A : (p : ℤ) ∣ 2 * (x.val : ℤ) := by
          have hadd : (p : ℤ) ∣ ((x.val : ℤ) + (y.val : ℤ)) + ((x.val : ℤ) - (y.val : ℤ)) :=
            dvd_add hsum hpdiff'
          convert hadd using 1 <;> ring
        rcases hpZ.dvd_mul.1 h2A with h2 | hA
        · have hp2' : p ∣ 2 := by exact_mod_cast h2
          rcases (Nat.dvd_prime Nat.prime_two).1 hp2' with h1 | h2'
          · have h2le := hp.two_le; omega
          · exact hp2 h2'
        · have hpA2 : (p : ℤ) ^ 2 ∣ (x.val : ℤ) ^ 2 := by
            obtain ⟨t, ht⟩ := hA
            use t ^ 2
            rw [ht]; ring
          have hp1 : (p : ℤ) ∣ (1 : ℤ) := by
            have hd1 : (p : ℤ) ^ 2 ∣ ((x.val : ℤ) ^ 2 + 1) - (x.val : ℤ) ^ 2 :=
              dvd_sub hdaZ hpA2
            have hd2 : (p : ℤ) ^ 2 ∣ (1 : ℤ) := by
              convert hd1 using 1 <;> ring
            exact dvd_trans (dvd_pow_self (p : ℤ) (by norm_num : (2 : ℕ) ≠ 0)) hd2
          have hp1' : p ∣ 1 := by exact_mod_cast hp1
          have h2le := hp.two_le
          have hpe1 : p = 1 := Nat.dvd_one.1 hp1'
          omega
      have hps' : (p : ℤ) ∣ s := by
        rcases hpZ.dvd_mul.1 hps with h | h
        · exact h
        · exact absurd h hnsum
      obtain ⟨t, ht⟩ := hps'
      have hAB : (p : ℤ) ^ 2 ∣ (x.val : ℤ) - (y.val : ℤ) := by
        use t
        rw [hs, ht]; ring
      have hcast0 : (((x.val : ℤ) - (y.val : ℤ) : ℤ) : ZMod (p ^ 2)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact_mod_cast hAB)
      have hxy2 : (x.val : ZMod (p ^ 2)) = (y.val : ZMod (p ^ 2)) := by
        have hsub : (x.val : ZMod (p ^ 2)) - (y.val : ZMod (p ^ 2)) = 0 := by
          have h := hcast0
          push_cast at h
          exact h
        exact sub_eq_zero.1 hsub
      rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, hxy2]
    exact (Finset.card_le_card_of_injOn φ hmaps hinj).trans (roots_mod_p_card_le p)

/-! ## F3, factored through the mod-25 coordinate

A type in `C` is glued to itself and to every type of the same mod-25 class
through 25; this depends only on the common residue `r ∈ {7, 18}`. A type
outside `C` is never glued to itself: its mod-4, mod-9 coordinates are
covered by `f1_mod4`, `f1_mod9`, and its mod-25 coordinate by
`f1_mod25_roots`. Gluing through 25 across different mod-25 residues is
impossible (`f3_cross25`), so a `C`-type and a non-`C`-type, or a 7-class
and an 18-class type, can be glued only through 4 or 9. -/

/-- F3: for `r ∈ {7, 18}`, `25 ∣ r^2 + 1` (self- and same-class gluing). -/
theorem f3_same25 : (List.range 25).all (fun r =>
  !(r == 7 || r == 18) || (r * r + 1) % 25 == 0) = true := by
  decide

/-- F3: for `r ∈ {7, 18}` and `q ≠ r`, `25 ∤ r*q + 1` (no cross-class or
    C-vs-non-C gluing through 25). -/
theorem f3_cross25 : (List.range 25).all (fun r => (List.range 25).all (fun q =>
  !(r == 7 || r == 18) || q == r || (r * q + 1) % 25 != 0)) = true := by
  decide

/-! ## The two extremal configurations (finite content of Prop. extremal /
    Prop. only-two)

A mixed pair of residue classes `u ≡ 7`, `v ≡ 18 (mod 25)` modulo 100 gives
an admissible two-class set iff `u^2 + 1`, `v^2 + 1`, `u*v + 1` are each
divisible by 4 or 25: divisibility by 9 cannot hold for all lifts to
mod 900 (the mod-9 coordinates range freely by CRT, `f1_mod9` kills the
diagonal, and `a = b = 0` gives `a*b + 1 ≡ 1 (mod 9)` for the cross term).
The CRT-lift argument is the queued glue lemma; the classification itself
is finite and checked here. Matches the referee's `local_facts.py`, which
found the same two pairs by the mod-900 brute force. -/

/-- The 4-or-25 obstruction test for a mod-100 class pair. -/
def classPairOk (u v : ℕ) : Bool :=
  ((u * u + 1) % 4 == 0 || (u * u + 1) % 25 == 0) &&
  ((v * v + 1) % 4 == 0 || (v * v + 1) % 25 == 0) &&
  ((u * v + 1) % 4 == 0 || (u * v + 1) % 25 == 0)

/-- Exactly two mixed mod-100 class pairs pass: `(7, 93)` and `(57, 43)`,
    i.e. the configurations `{7, 93}` and `{43, 57}` of the paper. -/
theorem only_two_pairs :
    ((List.range 100).filter (fun u => u % 25 == 7)).flatMap (fun u =>
      ((List.range 100).filter (fun v => v % 25 == 18)).filterMap (fun v =>
        if classPairOk u v then some (u, v) else none))
    = [(7, 93), (57, 43)] := by
  decide

end Erdos848
