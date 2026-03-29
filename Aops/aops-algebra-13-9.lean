import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.QuadraticDiscriminant

open Complex

/-- Art of Problem Solving
Algebra
Problem 13.9

z^2 + 6iz = -7
-/
lemma algebra_13_9 (z : ℂ) : z^2 + 6 * I * z = -7 ↔ z = I ∨ z = - 7 * I := by
  constructor
  . intro h
    have : 1 * z * z + 6 * I * z = -7 := by
      rw [← h]
      simp
      ring_nf
    have : 1 * z * z + 6 * I * z + 7 = 0 := by
      rw [this]
      simp
    have Q := @quadratic_eq_zero_iff
      ℂ _ _ 1 (6 * I) 7
      (Ne.symm (zero_ne_one' ℂ)) (8 * I)
      (by
        unfold discrim
        simp
        ring_nf
        rw [I_sq]
        simp
        ring_nf
      ) z
    rw [mul_assoc] at this
    rw [Q] at this
    simp at this
    cases this with
    |inl h => left;rw [h];ring_nf;simp;exact Nat.cast_one
    |inr h => right;rw [h];ring_nf
  . intro h
    cases h with
    |inl hl =>
      subst hl
      ring_nf
      rw [I_sq]
      simp
    |inr hr =>
      subst hr
      ring_nf
      rw [I_sq]
      simp
      rfl
