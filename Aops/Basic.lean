/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# OML Sample Problems 2017

https://drive.google.com/file/d/1nZ7VXjXISWQnUQNZiVDlBqbKDpxhhhyQ/view
-/

/-- Sample Problem A-1. -/
lemma event1_A_1 : let f := (fun x : ℝ => - x^2 + 2 * x - 3)
    f 1 = - 2 ∧ (∀ x, f x ≤ f 1)
     := by
  intro f
  constructor
  · simp [f]
    linarith
  · intro x
    simp [f]
    suffices x ^ 2 - 2 * x + 1 ≥ 0 by
        linarith
    suffices (x - 1) ^ 2 ≥ 0 by
        convert this
        ring_nf
    positivity

/-- Sample Problem A-2. -/
lemma event1_A_2 : let f := (fun x : ℝ => - x^2 + 2 * x - 3)
    ∀ y, (y ≤ -2 ↔ ∃ x, f x = y) := by
  intro f y
  constructor
  · intro hy
    simp [f]
    use 1 + √(- 2 - y)
    ring_nf
    have : -2 - y ≥ 0 := by linarith
    rw [Real.sq_sqrt this]
    linarith
  · simp
    have := event1_A_1
    unfold f
    simp at this ⊢
    intro x h
    have := this.2 x
    linarith

/-- Sample Problem A-3. -/
lemma event1_A_3 (x : ℝ) :
    (x-4)^2 - 5*(x-4)+6 = 0 ↔ x = 6 ∨ x = 7 := by
  constructor
  · intro h
    set y := x - 4 -- since `x` only appears via `x-4`.
    have : (y - 5 / 2)^2 - (5 / 2)^2 + 6 = 0 := by
        rw [← h]
        repeat rw [pow_two]
        ring_nf
    set z := y - 5/2 -- since `y` only appears via `y-5/2`
    have : z ^ 2 = (1 / 2) ^ 2 := by linarith
    have : z = √ ((1 / 2) ^ 2) ∨ z = - √ ((1 / 2) ^ 2) := by
        refine mul_self_eq_mul_self_iff.mp ?_
        convert this
        rw [pow_two]
        simp
        ring_nf
    simp at this
    unfold z at this
    ring_nf at this
    have : y = 3 ∨ y = 2 := by
        cases this with
        | inl h => left; linarith
        | inr h => right;linarith
    unfold y at this
    cases this with
    | inl h => right;linarith
    | inr h => left;linarith
  · intro h
    cases h with
    | inl h => subst x;ring_nf
    | inr h => subst x;ring_nf

/-- Sample Problem B-1. -/
lemma event1_B_1 (t c : ℝ) (ht : t = -4 + √7) (hc: 2*t^2+16*t+c=0) : c = 18 := by
  subst t
  field_simp at hc
  ring_nf at hc
  rw [Real.sq_sqrt] at hc
  linarith
  simp

/-- Sample Problem B-2, "real numbers version". -/
lemma event1_B_2_real (k : ℝ) (p : ℝ → ℝ)
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

/-- Sample Problem B-2, "complex numbers version". -/
lemma event1_B_2_complex (k : ℝ) (p : ℂ → ℂ)
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

noncomputable def vertex_x (a b : ℝ) : ℝ :=
    -b / (2*a)

noncomputable def vertex (a b c : ℝ) : ℝ × ℝ :=
    (vertex_x a b, (fun x => a*x^2+b*x+c) (vertex_x a b))

/-- Sample Problem C-1. -/
lemma event1_C_1 (a b c : ℝ) (h : vertex a b c = (2,3))
    (hf : (fun x => a*x^2+b*x+c) 4 = 1)
    :
    (a,b,c) = (-1/2, 2, 1) := by
  unfold vertex vertex_x at h
  simp at h hf ⊢
  by_cases ha : a = 0
  · subst a;simp at h
  field_simp at *
  have : b = - 4 * a := by linarith
  subst b
  field_simp at *
  ring_nf at hf
  subst hf
  simp at *
  constructor
  · linarith
  · linarith

lemma event1_C_2 (x y : ℝ) (h : x + y = 10) :
    x^2 + y^2 ≥ 50 := by
  have g₀ : y = 10 - x := by linarith
  rw [g₀]
  ring_nf
  suffices 50 - x * 10 + x ^ 2 ≥ 25 by linarith
  suffices (x - 5)^2 ≥ 0 by linarith
  positivity

lemma event3_B_1 (a : ℕ → ℤ)
    (h₀ : a 0 = 3)
    (h₁ : a 1 = 10)
    (h : ∀ n, a (n+2) = 2 * a (n+1) - a n) :
    a (100-1) = 696 := by  -- since the 100th term is term number 99 if we start at 0
  have : ∀ n, a n = 3 + 7 * n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n = 0
        · subst n; simp; exact h₀
        · obtain ⟨m,hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn
          subst n
          by_cases hm : m = 0
          · subst m
            simp
            exact h₁
          · obtain ⟨n,hn⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero hm
            subst m
            rw [h]
            rw [ih (n+1) (by omega)]
            rw [ih n (by omega)]
            simp
            omega
  specialize this (100-1)
  simp at this ⊢
  exact this

open Finset in
/-- e,m,s = English, Math, Science -/
lemma event3_c (n : ℕ) (e m s : Finset (Fin n))
    (h₀ : #e = 100)
    (h₁ : #m ≤ 80)
    -- (h₂ : #s = 60) -- not needed
    (h₃ : #(e ∩ m ∩ sᶜ) = 40)
    (h₄ : #(e ∩ mᶜ ∩ s) = 10)
    (h₅ : #(eᶜ ∩ m ∩ s) = 35) :
    45 ≤ #(e ∩ mᶜ ∩ sᶜ) ∧ #(e ∩ mᶜ ∩ sᶜ) ≤ 50 := by
  let x₀₀₀ := #(eᶜ ∩ mᶜ ∩ sᶜ)
  let x₀₀₁ := #(eᶜ ∩ mᶜ ∩ s)
  let x₀₁₀ := #(eᶜ ∩ m ∩ sᶜ)
  let x₀₁₁ := #(eᶜ ∩ m ∩ s)
  let x₁₀₀ := #(e ∩ mᶜ ∩ sᶜ)
  let x₁₀₁ := #(e ∩ mᶜ ∩ s)
  let x₁₁₀ := #(e ∩ m ∩ sᶜ)
  let x₁₁₁ := #(e ∩ m ∩ s)
  have g₀ : #e = x₁₀₀ + x₁₀₁ + x₁₁₀ + x₁₁₁ := by
    simp [x₁₀₀, x₁₀₁, x₁₁₀, x₁₁₁]
    have : e = (e ∩ (mᶜ ∩ sᶜ)) ∪ (e ∩ (mᶜ ∩ s)) ∪ (e ∩ (m ∩ sᶜ)) ∪ (e ∩ (m ∩ s)) := by
        ext;simp;tauto
    nth_rw 1 [this]
    repeat
        rw [card_union]
        simp
    rw [show e ∩ (mᶜ ∩ (s ∩ (e ∩ (m ∩ sᶜ)))) = ∅ by (ext;simp;tauto)]
    rw [show mᶜ ∩ (sᶜ ∩ (e ∩ (mᶜ ∩ s) ∪ e ∩ (m ∩ sᶜ))) = ∅ by (ext;simp;tauto)]
    rw [show (e ∩ (mᶜ ∩ sᶜ) ∪ (e ∩ (mᶜ ∩ s) ∪ e ∩ (m ∩ sᶜ))) ∩ (e ∩ (m ∩ s)) = ∅ by (ext;simp;tauto)]
    simp
    abel_nf

  have g₀ : #m = x₀₁₀ + x₀₁₁ + x₁₁₀ + x₁₁₁ := by
    simp [x₀₁₀, x₀₁₁, x₁₁₀, x₁₁₁]
    have : m = (e ∩ (m ∩ s)) ∪ (e ∩ (m ∩ sᶜ)) ∪ (eᶜ ∩ (m ∩ s)) ∪ (eᶜ ∩ (m ∩ sᶜ)) := by
        ext;simp;tauto
    nth_rw 1 [this]
    repeat
        rw [card_union]
        simp
    rw [
        show (e ∩ (m ∩ (sᶜ ∩ (eᶜ ∩ (m ∩ s))))) = ∅ by (ext;simp;tauto),
        show (e ∩ (m ∩ (s ∩ (e ∩ (m ∩ sᶜ) ∪ eᶜ ∩ (m ∩ s))))) = ∅ by (ext;simp;tauto),
        show ((e ∩ (m ∩ s) ∪ (e ∩ (m ∩ sᶜ) ∪ eᶜ ∩ (m ∩ s))) ∩ (eᶜ ∩ (m ∩ sᶜ))) = ∅ by (ext;simp;tauto)]
    simp
    abel_nf
  have g₀ : #s = x₀₀₁ + x₀₁₁ + x₁₀₁ + x₁₁₁ := by
    simp [x₀₀₁, x₁₀₁, x₀₁₁, x₁₁₁]
    have : s = (e ∩ (m ∩ s)) ∪ (e ∩ (mᶜ ∩ s)) ∪ (eᶜ ∩ (m ∩ s)) ∪ (eᶜ ∩ (mᶜ ∩ s)) := by
        ext;simp;tauto
    nth_rw 1 [this]
    repeat
        rw [card_union]
        simp
    rw [
        show e ∩ (mᶜ ∩ (s ∩ (eᶜ ∩ (m ∩ s)))) = ∅ by (ext;simp;tauto),
        show e ∩ (m ∩ (s ∩ (e ∩ (mᶜ ∩ s) ∪ eᶜ ∩ (m ∩ s)))) = ∅ by (ext;simp;tauto),
        show (e ∩ (m ∩ s) ∪ (e ∩ (mᶜ ∩ s) ∪ eᶜ ∩ (m ∩ s))) ∩ (eᶜ ∩ (mᶜ ∩ s)) = ∅ by (ext;simp;tauto)]
    simp
    abel_nf
  constructor
  · linarith
  · linarith

open Finset in
lemma event3_c_lower_sharp :
 ∃ (n : ℕ) (e m s : Finset (Fin n)),
    (#e = 100) ∧
    (#m = 80) ∧
    (#s = 60) ∧
    (#(e ∩ m ∩ sᶜ) = 40) ∧
    (#(e ∩ mᶜ ∩ s) = 10) ∧
    (#(eᶜ ∩ m ∩ s) = 35) ∧
    45 = #(e ∩ mᶜ ∩ sᶜ) := by
  use 145
  use Finset.Ico 0 100
  use Finset.Ico 55 (55+80)
  use (Finset.Ico 45 (45+10+5)) ∪ (Finset.Icc 100 144)
  simp

  constructor
  · rw [card_union]
    simp
    have : #(Ico (45 : Fin 145) 60 ∩ Icc 100 144) = 0 := by sorry
    simp_rw [this]
  · have g₀ : (Ico (0 : Fin 145) 100) ∩ (Ico 55 135 ∩ ((Ico 45 60)ᶜ ∩ (Icc 100 144)ᶜ))
            = Ico 60 100 := by
        ext x
        simp
        constructor
        · intro h
          constructor
          · apply h.2.2.1
            refine le_trans ?_ h.2.1.1
            simp
          · tauto
        · intro h
          constructor
          · tauto
          · constructor
            · constructor
              · refine le_trans ?_ h.1
                simp
              · apply lt_trans h.2
                simp
            · constructor
              · tauto
              · intro h₀
                exfalso
                have : (100 : Fin 145) < 100 := lt_of_le_of_lt h₀ h.2
                simp at this

    constructor
    · rw [g₀]
      simp
    · constructor
      · sorry
      · constructor
        · sorry
        · sorry
