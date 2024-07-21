import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.QuadraticDiscriminant

/- Art of Problem Solving
Algebra
Problem 13.9

z^2 + 6iz = -7
-/

example (z : ℂ) : z^2 + 6 * Complex.I * z = -7 ↔ z = Complex.I ∨ z = - 7 * Complex.I := by
  constructor
  . intro h
    have : 1 * z * z + 6 * Complex.I * z = -7 := by
      rw [← h]
      simp
      ring_nf
    have : 1 * z * z + 6 * Complex.I * z + 7 = 0 := by
      rw [this]
      simp
    have Q := @quadratic_eq_zero_iff
      ℂ _ _ 1 (6 * Complex.I) 7
      (Ne.symm (zero_ne_one' ℂ)) (8 * Complex.I)
      (by
        unfold discrim
        simp
        ring_nf
        rw [Complex.I_sq]
        simp
        ring_nf
      ) z
    rw [Q] at this
    simp at this
    cases this with
    |inl h => left;rw [h];ring_nf
    |inr h => right;rw [h];ring_nf
  . intro h
    cases h with
    |inl hl =>
      subst hl
      ring_nf
      rw [Complex.I_sq]
      simp
    |inr hr =>
      subst hr
      ring_nf
      rw [Complex.I_sq]
      simp
