/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# OML Sample Problems 2017

-/

lemma C_2 (x y : ℝ) (h : x + y = 10) :
    x^2 + y^2 ≥ 50 := by
  have g₀ : y = 10 - x := by linarith
  rw [g₀]
  ring_nf
  suffices 50 - x * 10 + x ^ 2 ≥ 25 by linarith
  suffices (x - 5)^2 ≥ 0 by linarith
  positivity


lemma A_1_and_A_2 : let f := (fun x : ℝ => - x^2 + 2 * x - 3)
    f 1 = - 2 ∧ (∀ x, f x ≤ f 1)
    ∧ ∀ y, y ≤ -2 → ∃ x, f x = y
     := by
  intro f
  constructor
  · simp [f]
    linarith
  · constructor
    intro x
    simp [f]
    suffices x ^ 2 - 2 * x + 1 ≥ 0 by
        linarith
    suffices (x - 1) ^ 2 ≥ 0 by
        convert this
        ring_nf
    positivity
    · intro y hy
      simp [f]
      use 1 + √(- 2 - y)
      ring_nf
      show -2 - (√(-2 - y)) ^ 2 = y
      have : -2 - y ≥ 0 := by linarith
      rw [Real.sq_sqrt this]
      linarith

lemma B_1 (t c : ℝ) (ht : t = -4 + √7) (hc: 2*t^2+16*t+c=0) : c = 18 := by
  subst t
  field_simp at hc
  ring_nf at hc
  rw [Real.sq_sqrt] at hc
  linarith
  simp

lemma B_2 (k : ℝ) (p : ℝ → ℝ)
  (hp : p = fun x : ℝ => 3 * x^2 + 6 * x + k) :
  (k < 3 ↔ ∃ a b, a ≠ b ∧ p a = 0 ∧ p b = 0)
  ∧
  (k ≤ 3 ↔ ∃ a, p a = 0)
  := by
  have g₀ : k < 3 ↔ ∃ a b, a ≠ b ∧ p a = 0 ∧ p b = 0 := by

    constructor
    · intro hk
      use √(1-k/3)-1
      use -√(1-k/3)-1
      constructor
      suffices √(1 - k / 3) ≠ -√(1 - k / 3) by
        contrapose! this
        linarith
      refine self_ne_neg.mpr ?_
      refine (Real.sqrt_ne_zero ?_).mpr ?_
      linarith
      linarith
      constructor <;> (
      rw [hp]
      simp
      rw [pow_two]
      ring_nf
      rw [Real.sq_sqrt]
      linarith
      linarith)
    intro ⟨a,b,hab⟩
    rw [hp] at hab
    simp at hab
    have h₀a : a ^ 2 + 2 * a + k / 3 = 0 := by linarith
    have h₀b : b ^ 2 + 2 * b + k / 3 = 0 := by linarith
    have h₁a : a ^ 2 + 2 * a = (a + 1) ^ 2 - 1 := by rw [pow_two];linarith
    have h₁b : b ^ 2 + 2 * b = (b + 1) ^ 2 - 1 := by rw [pow_two];linarith
    rw [h₁a] at h₀a
    rw [h₁b] at h₀b
    have h₂a : (a + 1) ^ 2 = 1 - k / 3 := by linarith
    have h₂b : (b + 1) ^ 2 = 1 - k / 3 := by linarith

    by_cases H : a = -1
    · subst a
      simp at h₂a
      have : k = 3 := by linarith
      subst this
      simp at h₂b
      exfalso
      apply hab.1
      linarith
    have h₃ : 0 ≤ 1 - k / 3 := by rw [← h₂a];positivity
    field_simp at h₃
    simp at h₃
    by_cases G : k = 3
    · subst k
      simp at h₂b h₂a
      exfalso
      apply hab.1
      linarith
    exact Std.lt_of_le_of_ne h₃ G


  constructor
  tauto
  have h₀: k = 3 → ∃ a, p a = 0 := by
    intro hk
    subst k
    rw [hp]
    simp
    use -1
    simp
    linarith
  constructor
  intro hk
  have : k < 3 ∨ k = 3 := by exact Std.le_iff_lt_or_eq.mp hk
  cases this <;> tauto
  intro ⟨a,ha⟩
  rw [hp] at ha
  simp at ha
  have : a ^ 2 + 2 * a + k / 3 = 0 := by linarith
  have : (a + 1) ^ 2 - 1 + k / 3 = 0 := by linarith
  have : (a + 1) ^ 2 = 1 - k / 3 := by linarith
  have : 0 ≤ 1 - k / 3 := by rw[← this];positivity
  linarith

/-- This is more directly in the spirit of question
B-2. -/
lemma B_2' (k : ℝ) (p : ℂ → ℂ)
  (hp : p = fun x : ℂ => 3 * x^2 + 6 * x + k) :
  k ≤ 3 ↔ ∀ z, p z = 0 → z.im = 0 := by
  constructor
  · intro hk z hz
    rw [hp] at hz
    simp at hz
    have : (3 * z ^ 2 + 6 * z) / 3 + ↑k / 3 = 0 / 3 := by
      rw [← hz]
      ring_nf
    have : z ^ 2 + 2 * z + k / 3 = 0 := by
      ring_nf at this
      simp at this
      rw [← this]
      ring_nf
      field_simp
      suffices z * (2 + z) * 3 = z * 3 * (2 + z * ↑1) by
        rw [this]
        simp
        left
        have : (@Nat.cast ℂ Mathlib.Meta.NormNum.instAddMonoidWithOne'.toNatCast 1 : ℂ)
          = 1 := by exact Nat.cast_one
        rw [this]
        simp
        rfl
      ring_nf
    have : (z + 1) ^ 2 - 1 + k / 3 = 0 := by
      rw [← this]
      ring_nf
    have : (z + 1) ^ 2 - 1 = - (k / 3) := by
      exact Eq.symm (neg_eq_of_add_eq_zero_left this)
    have : (z + 1) ^ 2 - 1 + 1 = - (k / 3) + 1 := by
      rw [this]

    have : (z + 1) ^ 2 = 1 - k / 3 := by
      simp at this
      rw [this]
      field_simp
      ring_nf
    have h₀ : ((z + 1) ^ 2).im = 0 := by
      rw [this]
      simp
    have : 0 ≤ ((z + 1) ^ 2).re := by
      rw [this]
      simp
      linarith
    have (a b : ℂ) (him : a.im = b.im) (hre : a.re = b.re) : a = b := by exact Complex.ext hre him
    have (w : ℂ) (hw₀ : (w ^ 2).im = 0) (hw₁ : 0 ≤ (w ^ 2).re) : w.im = 0 := by
      have h_im : 2 * w.re * w.im = 0 := by
        rw [pow_two] at hw₀ hw₁
        rw [Complex.mul_re] at hw₁
        rw [Complex.mul_im] at hw₀
        linarith
      simp at h_im
      cases h_im with
      | inl h =>
        have h_re :
            w.re^2 - w.im^2 = (w^2).re := by
          simp [pow_two]
        rw [←  h_re, h] at hw₁
        simp at hw₁
        rw [h] at h_re
        simp at h_re
        linarith
      | inr h => tauto

    have : (z + 1).im = 0 := by
      apply this
      tauto
      tauto
    simp at this
    tauto

  contrapose!
  intro h
  set γ := 1 - k / 3
  -- Now we should use complex numbers directly, no Real.sqrt:
  use √(-γ) * Complex.I - 1
  rw [hp]
  simp
  have hγ : γ < 0 := by simp [γ];linarith
  have hγ : -γ > 0 := by exact Left.neg_pos_iff.mpr hγ
  rw [pow_two]
  constructor
  · ring_nf
    rw [Complex.I_sq]
    simp
    suffices -3 + -(Complex.ofReal √(-γ) ^ 2 * 3) = - ↑k by
      rw [this];simp
    suffices -(Complex.ofReal √(-γ) ^ 2 * 3) = 3 - ↑k by
      rw [this]
      ring_nf
    rw [← neg_mul]
    show -Complex.ofReal √(-γ) ^ 2 * 3 = 3 - ↑k
    suffices -Complex.ofReal √(-γ) ^ 2 * 3 / 3 = (3 - ↑k) / 3 by
      field_simp at this
      rw [← this]
      simp
    have (z : ℂ) : z * 3 / 3 = z := by simp
    rw [this]
    have : (3 - Complex.ofReal k) / 3 = γ := by
      simp [γ]
      field_simp
    rw [this]
    rw [neg_eq_iff_eq_neg]
    rw [← Complex.ofReal_neg]
    rw [pow_two]
    rw [← Complex.ofReal_mul]
    congr
    refine Real.mul_self_sqrt ?_
    linarith

  exact Real.sqrt_ne_zero'.mpr hγ
