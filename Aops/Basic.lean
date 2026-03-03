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
