import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/- Example inspired by an Art of Problem Solving: Algebra section -/
example (f : ℤ → ℤ → ℤ) (g h : ℤ → ℤ) :
  (∃ c, ∀ x y, f x y = c + g x + h y)
  ↔
  (∃ g₀ h₀ : ℤ → ℤ, ∀ x y,
    f x y = (g₀ x) + (h y) ∧
    f x y = (g x) + (h₀ y))
  := by
    constructor
    . intro hyp
      obtain ⟨c,hc⟩ := hyp
      exists (λ x ↦ c + g x)
      exists (λ x ↦ c + h x)
      simp
      intro x y
      let Q := hc x y
      constructor
      . tauto
      rw [Q]
      ring

    . intro hyp
      obtain ⟨g₀,hg₀⟩ := hyp
      obtain ⟨h₀,hh₀⟩ := hg₀
      exists h₀ 0 - h 0
      intro x y
      have H₀ : ∀ x y, f x y = g₀ x + h  y := λ x y ↦ (hh₀ x y).1
      have H₁ : ∀ x y, f x y = g  x + h₀ y := λ x y ↦ (hh₀ x y).2
      have H₂ : ∀ x y, g₀ x + h y = g x + h₀ y := λ x y ↦ Eq.trans (H₀ x y).symm (H₁ x y)
      have H₃ : ∀ x y, g x - g₀ x = h y - h₀ y := by
        intro x y
        suffices g x - g₀ x + g₀ x = h y - h₀ y + g₀ x by
          exact (Int.add_right_inj (g x - g₀ x) (h y - h₀ y) (g₀ x)).mp this
        simp
        suffices g x + h₀ y = h y - h₀ y + g₀ x + h₀ y by
          exact (Int.add_right_inj (g x) (h y - h₀ y + g₀ x) (h₀ y)).mp this
        rw [← H₂]
        ring
      let H₄ : g x - g₀ x = h 0 - h₀ 0 := H₃ x 0
      suffices f x y = g x + h y - (h 0 - h₀ 0) by
        rw [this]
        ring_nf
      rw [← H₄]
      simp
      rw [H₀]
      ring


example (x y z : Nat → Nat) :
  (∃ c, ∀ t, x t = c * y t * z t)
  ↔
  (∀ y₀, ∃ c, ∀ t, y t = y₀ → x t = c * (z t))
  ∧
  (∀ z₀, ∃ c, ∀ t, z t = z₀ → x t = c * (y t))
  := by
    constructor
    intro h
    obtain ⟨c,hc⟩ := h
    constructor
    . intro y₀
      exists c * y₀
      intro t ht
      rw [← ht]
      exact hc t
    . intro z₀
      exists c * z₀
      intro t ht
      rw [← ht]
      rw [hc t]
      exact Nat.mul_right_comm c (y t) (z t)
    intro h
    let Qy := h.1 (y 0)
    obtain ⟨dy,hdy⟩ := Qy
    let Ry := hdy 0 rfl
    -- let Qz := h.2 (z 0)
    -- obtain ⟨dz,hdz⟩ := Qz
    -- let Rz := hdz 0 rfl
    exists dy / y 0
    intro t
    let Qt := h.1 (y t)
    obtain ⟨ct,hct⟩ := Qt
    let Rt := hct t rfl
    rw [Rt]
    sorry
