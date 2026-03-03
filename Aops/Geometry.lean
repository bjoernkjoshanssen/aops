import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Reflection
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic --  Orientation.oangle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine --  EuclideanGeometry.oangle
-- import Mathlib
/-!

## Introduction to Geometry
Richard Rusczyk
-/

open Real

/-- Converting degrees into radians. -/
noncomputable def deg : ℕ → ℝ := fun n => (n:ℝ) / 360 * 2 * π
/-- Exercise 1.2.2 -/
theorem rusczyk_1_1_2 {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] {A B M N : P}
  (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ B M) (h : dist B N = 4) :
  dist A B = 16 := by
    subst M N
    rw [dist_left_midpoint, dist_right_midpoint, norm_ofNat] at h
    linarith

/-- Making A B M N have L^2 type ensures that `dist` uses the right distance. -/
theorem rusczyk_1_1_2' {d : ℕ} {A B M N : PiLp 2 fun _ : Fin d => ℝ}
  (hM : M = midpoint ℝ A B)
  (hN : N = midpoint ℝ B M)
  (h : dist B N = 4) :
  dist A B = 16 := rusczyk_1_1_2 hM hN h

/-- A concrete example of `rusczyk_1_1_2'`. -/
example : (![(3:ℝ),1]) = midpoint ℝ ![1,0] ![5,2] := by
  simp [midpoint, AffineMap.lineMap]
  grind


example : dist (WithLp.toLp 2 ![(0 : ℝ),0]) (WithLp.toLp 2 ![3,4]) = 5 := by
  simp
  rw [EuclideanSpace.dist_eq]
  simp
  refine Real.sqrt_eq_cases.mpr ?_
  grind

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := { out := finrank_euclideanSpace_fin }
-- instance : Fact (Module.finrank ℝ (Fin (Nat.succ 1) → ℝ) = 2) := { out := finrank_euclideanSpace_fin }

instance : Fact (Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2) := { out := finrank_euclideanSpace_fin }

/- By Eric Wieser at https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Euclidean.20space.20is.20oriented/
-/
-- noncomputable instance (n : Type*) [Fintype n] [DecidableEq n] :
--   Module.Oriented ℝ (EuclideanSpace ℝ n) n :=
--   ⟨Basis.orientation <| Pi.basisFun _ _⟩

-- noncomputable instance : Module.Oriented ℝ (Fin (Nat.succ 1) → ℝ) (Fin 2) :=
--     ⟨Basis.orientation <| Pi.basisFun _ _⟩

noncomputable instance :  InnerProductSpace ℝ (WithLp 2 (Fin (Nat.succ 1) → ℝ))
 := PiLp.innerProductSpace fun _ ↦ ℝ


noncomputable instance : Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) := by
  refine { positiveOrientation := ?_ }
  refine Module.Basis.orientation $ PiLp.basisFun 2 ℝ (Fin 2)

-- have : angle X O Y = ∠ X O Y := rfl

-- noncomputable def β := Basis.orientation <| PiLp.basisFun 2 ℝ (Fin 2)

-- open Orientation
open EuclideanGeometry

/--
Problem 2.3.
Given that ∠WOY = 60° and ∠WOX = 20°, find ∠XOY.

W   X
|  /
| /
O --- Y

 where OX is between OW and OY.

 The angle ∡ can be written oangle.
  -/
theorem rusczyk_problem_2_3 {O W X Y : EuclideanSpace ℝ (Fin 2)}
    (hW : W ≠ O) (hX : X ≠ O) (hY : Y ≠ O)
    (h₁ : ∡ W O Y = π / (3:ℝ))
    (h₂ : ∡ W O X = π / (9:ℝ)) :
    ∡ X O Y = (2:ℝ) / 9 * π := by
  have : ↑(π / 9) + ∡ X O Y = ↑(π / 3) :=
    h₁ ▸ h₂ ▸ oangle_add hW hX hY
  rw [eq_sub_of_add_eq' this]
  rw [← Angle.coe_sub]
  congr
  linarith



theorem rusczyk_problem_2_4 {P Q R : EuclideanSpace ℝ (Fin 2)}
    (h₁ : ∡ P Q R = deg 40) :
    ∡ R Q P = deg 320 := by
  rw [oangle_rev P Q R]
  rw [h₁]
  simp [deg]
  refine neg_eq_of_add_eq_zero_right ?_
  rw [← Angle.coe_add]
  refine Angle.coe_eq_zero_iff.mpr ?_
  use 1
  simp
  linarith


theorem rusczyk_problem_2_6  {d : ℕ} (A B O : EuclideanSpace ℝ (Fin d))
    (h : Sbtw ℝ A O B) :
    angle A O B = deg 180 := by
  convert Sbtw.angle₁₂₃_eq_pi h using 1
  simp [deg]
  norm_num



/--
Rusczyk Problem 2.7

W ? Y
 \ /
  X  55°
 / \
V   Z

Given ∠ YXZ = 55°, find ∠ WXY.
(The point V is not relevant.)
-/
theorem rusczyk_problem_2_7 {X W Y Z : EuclideanSpace ℝ (Fin 2)}
    (hW : W ≠ X) (hY : Y ≠ X) (hZ : Z ≠ X)
    (h₀ : Sbtw ℝ W X Z)
    (h₁ : ∡ Y X Z = deg 55) :
    ∡ W X Y = deg 125 := by
  unfold deg at *
  rw [eq_sub_of_add_eq $ oangle_add hW hY hZ]
  rw [h₁]
  rw [oangle_eq_pi_iff_sbtw.mpr h₀]
  rw [← Angle.coe_sub]
  congr
  linarith


/--

Rusczyk Problem 2.8:

L  ✓ M
  \ /
   P  72°
  / \
O     N

∠ MPN = 72°
Find ∠ LPO.

Solution: it is 72° but in terms of oriented angles we want
to prove `oangle O P L` = ∠ OPL = 72°.
-/

theorem rusczyk_problem_2_9 {L M N O P : EuclideanSpace ℝ (Fin 2)}
    (hL : L ≠ P) (hM : M ≠ P) (hN : N ≠ P) (hO : O ≠ P)
    (hb₀ : Sbtw ℝ L P N) (hb₁ : Sbtw ℝ M P O) :
    ∡ O P L = ∡ M P N := by
  have h₀ := oangle_add hO hL hM
  have h₁ := oangle_add hL hM hN
  rw [oangle_eq_pi_iff_sbtw.mpr hb₁.symm] at h₀
  rw [oangle_eq_pi_iff_sbtw.mpr hb₀, ← h₀, add_comm, add_left_inj] at h₁
  exact h₁.symm


theorem rusczyk_problem_2_8  {L M N O P : EuclideanSpace ℝ (Fin 2)}
    (hL : L ≠ P) (hM : M ≠ P) (hN : N ≠ P) (hO : O ≠ P)
    (hb₀ : Sbtw ℝ L P N) (hb₁ : Sbtw ℝ M P O)
    (h : ∡ M P N = deg 72) :
    ∡ O P L = deg 72 := rusczyk_problem_2_9 hL hM hN hO hb₀ hb₁ ▸ h


theorem a_2_10
  {B D E F : EuclideanSpace ℝ (Fin 2)}
  (hE' : Sbtw ℝ D E F) (h : ∡ D E B = ↑(deg 113))
  (h₀ : D ≠ E) (h₁ : F ≠ E) (h₂ : B ≠ E) : ∡ B E F = ↑(deg 67) := by
  -- have g₀ := oangle_eq_pi_iff_sbtw.mpr hB'
  have g₁ := oangle_eq_pi_iff_sbtw.mpr hE'

  have g₂ := oangle_add h₂ h₁ h₀
  have g₃ := oangle_add h₀ h₁ h₂
  rw [h] at g₃
  rw [g₁] at g₃
  show ∡ B E F = ↑(deg 67)
  have g₄ : ∡ B E F + ∡ F E B = 0 := by
    rw [← oangle_self_left_right B E]
    exact oangle_add h₂ h₁ h₂
  -- have : ∠ B E F = - ∠ F E B := by apply?
  have g₅ := eq_sub_of_add_eq' g₃

  -- have h : ∡ B E D = π - deg 113 := by

  --   sorry
  -- rw [h] at g₂
  -- rw [g₁] at g₃
  show ∡ B E F = ↑(deg 67)
  rw [g₅] at g₄
  have : deg 67 = π - deg 113 := by
    unfold deg
    linarith
  rw [this]
  suffices ∡ B E F = - ↑(deg 113 - π) by
    rw [this]
    simp
  exact eq_neg_of_add_eq_zero_left g₄

/--
                G
               /
           w  / z
A ---------- B -------- C
         x  / y
           /
      113°/ (67° ✓)
D ------ E ----------- F
      b / c
       /
      H

-/
theorem rusczyk_problem_2_10 {m n : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    {A B C D E F G H : EuclideanSpace ℝ (Fin 2)}
    (hm : m = affineSpan ℝ {A, C})
    (hn : n = affineSpan ℝ {D, F})
    (h₁₂₄₅ : m.Parallel n)
    (hB : B ∈ m)
    (hE : E ∈ n)
    (hB' : Sbtw ℝ A B C)
    (hE' : Sbtw ℝ D E F)
    (h : ∡ D E B = deg 113)
    (h₀ : D ≠ E) (h₁ : F ≠ E)
    (h₂ : B ≠ E)
    (hmn : m ≠ n) :
    ∡ B E F = deg 67 ∧ ∡ F E H = deg 113 := by
  constructor
  apply a_2_10 hE' h h₀ h₁ h₂
  sorry


example (l m n : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    (h : l.Parallel m) (h₀ : m.Parallel n) : l.Parallel n := by
  exact AffineSubspace.Parallel.trans h h₀


open EuclideanGeometry



/-
                G
               /
           w  / z
A ---------- B -------- C
         x  / y
           /
      113°/ (67° ✓)
D ------ E --p--------- F
      b / c
       /
      H

-/
-- lemma angle_eq_of_parallel_and_transversal
--   {A B C D E F G H : EuclideanSpace ℝ (Fin 2)}
--   (h_parallel : (affineSpan ℝ {A, C}).Parallel (affineSpan ℝ {D, F}))
--   (h_parallel' : (affineSpan ℝ {A, B}).Parallel (affineSpan ℝ {D, E}))
--   (h : Sbtw ℝ A B C)
--   (h' : Sbtw ℝ D E F)
--   (hh : Sbtw ℝ G B H)
--   (h₀ : (affineSpan ℝ {G, H}).SSameSide A D) -- "sign the same"?
--   (g₀ : (affineSpan ℝ {A, D}).SSameSide B E) -- "sign the same"?
--   (g₁ : (affineSpan ℝ {B, E}).SSameSide A D)
--   :
--   ∡ D E B = ∡ A B G := by
--   have h₁ : (affineSpan ℝ {B, E}).Parallel (affineSpan ℝ {B, E}) := by
--     exact AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq.mpr rfl
--   have h₂ : (affineSpan ℝ {B, E}).Parallel (affineSpan ℝ {E, B}) :=
--     AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq.mpr
--       <| congrArg _ <| Set.pair_comm B E
--   have h₃ := EuclideanGeometry.two_zsmul_oangle_of_parallel (h₁₂₄₅ := h_parallel')
--     (h₃₂₆₅ := h₂.symm)
--   -- CAN USE THIS to go from `sameside` to `sameray`
--   have := (AffineSubspace.sSameSide_iff_exists_left (s := affineSpan ℝ {A, D})
--     (p₁ := A) (x := B) (y := E) (left_mem_affineSpan_pair ℝ A D)).mp g₀
--   obtain ⟨p,hp⟩ := this.2.2
--   -- ALSO USEFUL to go from `sameray` to `oangle 0` which can then be combined with `oangle.add`.
--   have :=  (Orientation.oangle_eq_zero_iff_sameRay (o := o)).mpr hp.2

--   have := (AffineSubspace.sSameSide_iff_exists_left (s := affineSpan ℝ {B, E})
--     (p₁ := B) (x := A) (y := D) (left_mem_affineSpan_pair ℝ B E)).mp g₁
--   obtain ⟨p,hp⟩ := this.2.2
--   have :=  (Orientation.oangle_eq_zero_iff_sameRay (o := o)).mpr hp.2


--   have :  o.oangle (A -ᵥ B) (D -ᵥ E) = 0 := by
--     convert this using 1
--     sorry



--   have : EuclideanSpace ℝ (Fin 2) := ![0,1]
--   have : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := by
--     -- the line y = π x + 1
--     refine AffineSubspace.mk' ![0,1] ?_
--     exact {
--       carrier := {x | x 1 = π * x 0} -- the direction
--       add_mem' := by
--         intro a b ha hb
--         simp at ha hb ⊢
--         rw [ha,hb]
--         linarith
--       zero_mem' := by
--         simp
--       smul_mem' := by
--         intro c x hx
--         simp at hx ⊢
--         rw [hx]
--         linarith
--     }
--   let v₁ := (![0,1] : EuclideanSpace ℝ (Fin 2)) - (![0,1] : EuclideanSpace ℝ (Fin 2))
--   let v₂ := (![0,1] : EuclideanSpace ℝ (Fin 2)) -ᵥ (![0,1] : EuclideanSpace ℝ (Fin 2))
--   have : v₁ = v₂ := by
--     show (![0,1] : EuclideanSpace ℝ (Fin 2)) - (![0,1] : EuclideanSpace ℝ (Fin 2))
--       = (![0,1] : EuclideanSpace ℝ (Fin 2)) -ᵥ (![0,1] : EuclideanSpace ℝ (Fin 2))
--     simp only [Nat.succ_eq_add_one, Nat.reduceAdd, sub_self, vsub_eq_sub]
--   have :  o.oangle (B -ᵥ A) (C -ᵥ A) = ∡ B A C := by
--     -- unfold EuclideanGeometry.oangle
--     rfl

--   -- have := @AffineSubspace.SSameSide.oangle_sign_eq --(hp₃p₄ := g₀) (p₁ := D) --(p₂ := B)
--   have :  (∡ A B E).sign = (∡ B E D).sign := by
--     -- have := @EuclideanGeometry.oangle_
--     sorry
--   repeat rw [two_smul] at h₃
--     --h_parallel this.symm

--   sorry

-- example : (![1,0] : EuclideanSpace ℝ (Fin 2))
--         = (![1,0] : EuclideanSpace ℝ (Fin 2))
--   := rfl

-- example (A B : EuclideanSpace ℝ (Fin 2)) : o.oangle A B = 0 := by sorry

-- example : o.oangle ((![1,0]) : EuclideanSpace ℝ (Fin 2))
--                    (![0,1] : EuclideanSpace ℝ (Fin 2)) = 0 := by sorry

def e₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(1:ℝ),0]

def e₂ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0,1]
def myB : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-1,0]

example (c : ℝ) (hc : 0 ≤ c) : o.oangle e₁ (c • e₁) = 0 := by
  have : e₁ = (1 : ℝ) • e₁ := by simp
  nth_rewrite 1 [this]
  exact Orientation.oangle_smul_smul_self_of_nonneg (r₂ := c) (r₁ := 1) (x := e₁) o
    (by simp) hc

-- example (c : ℝ) (hc : 0 ≤ c) : o.oangle e₁ (-c • e₁) = π := by
--   have : e₁ = (1 : ℝ) • e₁ := by simp
--   nth_rewrite 1 [this]
--   have := Orientation.oangle_smul_smul_self_of_nonneg (r₂ := c) (r₁ := 1) (x := e₁) o
--     (by simp) hc
--   simp

--   sorry


-- example : o.oangle e₁ e₂ = π /(2:ℝ):= by
--   unfold e₁ e₂
--   refine
--     (Orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero o ?_ ?_ ↑(π / 2)).mpr ?_

--   intro hc
--   rw [funext_iff] at hc
--   specialize hc 0
--   simp at hc

--   intro hc
--   rw [funext_iff] at hc
--   specialize hc 1
--   simp at hc

--   rw [show @norm (EuclideanSpace ℝ (Fin 2)) NormedAddCommGroup.toNorm ![0, 1]  = 1 by
--     sorry]
--   rw [show @norm (EuclideanSpace ℝ (Fin 2)) NormedAddCommGroup.toNorm ![1, 0]  = 1 by
--     sorry]
--   simp
--   symm

--   refine PiLp.ext ?_
--   intro i
--   fin_cases i
--   · simp
--     sorry
--   · simp
--     sorry

-- example : ∡ e₁ 0 ![0,1] = π /(2:ℝ) := by
--   -- have : ⟪e₁, e₂⟫ = 0 := sorry
--   unfold oangle e₁

--   refine
--     (Orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero o ?_ ?_ ↑(π / 2)).mpr ?_
--   · intro hc
--     simp at hc
--     rw [funext_iff] at hc
--     specialize hc 0
--     simp at hc
--   · intro hc
--     simp at hc
--     rw [funext_iff] at hc
--     specialize hc 1
--     simp at hc
--   · simp
--     ext j
--     fin_cases j
--     · simp
--       right
--       rw [Orientation.rotation_pi_div_two]

--       rw [Orientation.rightAngleRotation]
--       simp
--       rw [Orientation.rightAngleRotationAux₂]
--       simp
--       rw [Orientation.rightAngleRotationAux₁]
--       simp

--       rw [Orientation.areaForm]
--       simp

--       sorry
--     sorry


lemma angle_90 : ∠
  (WithLp.toLp 2 ![(1:ℝ),0])
  (WithLp.toLp 2 ![(0:ℝ),0])
  (WithLp.toLp 2 ![(0:ℝ),1]) = π / (2:ℝ) := by
  simp [angle, InnerProductGeometry.angle, inner]



lemma getMatrix (a b c d : ℝ) :
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.toMatrix
    ![!₂[a, b], !₂[c, d]] = ![![a, c], ![b, d]] := by
                ext i j;fin_cases i <;> fin_cases j <;> rfl

lemma getMatrix' (a b c d : ℝ) :
    ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.toMatrix
            ![!₂[a, b], !₂[c, d]]).det = a*d-b*c := by
        rw [Matrix.det_fin_two]
        repeat rw [getMatrix]
        simp
        rw [mul_comm]

lemma getMatrix'' (a b c d : ℝ) :
    ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det
    ![!₂[a, b], !₂[c, d]]) = a*d-c*b := by
  rw [Module.Basis.det_apply]
  rw [getMatrix']
  nth_rewrite 2 [mul_comm]
  rfl


lemma getMatrix''' (a b c d : ℝ) :
    ((o.areaForm !₂[a, b] !₂[c, d])) = a*d-c*b := by
        rw [o.areaForm_to_volumeForm]
        rw [o.volumeForm_robust]
        show (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det ![!₂[a, b], !₂[c, d]] = a * d - c * b
        exact getMatrix'' a b c d
        rfl

theorem calculate_angle' (a b c d : ℝ) :
    o.oangle !₂[a, b] !₂[c, d] = (a*c+b*d + (a*d-c*b)*Complex.I).arg := by
  simp [Orientation.oangle]
  simp [Orientation.kahler]
  simp [innerₛₗ]
  rw [getMatrix''']
  nth_rewrite 1 [mul_comm]
  nth_rewrite 2 [mul_comm]
  sorry

theorem calculate_angle : o.oangle !₂[(1:ℝ), 0] !₂[0, 1] = π / (2:ℝ) := by
  rw [calculate_angle']
  simp

lemma compl  (a b : ℝ) : ‖ Complex.mk a b‖ ^ 2 = a * a + b * b := by
        have := Complex.normSq_apply (Complex.mk a b)
        rw  [← Complex.normSq_mk]
        rw [Complex.normSq_eq_norm_sq]

lemma mynorm : ‖1 + Complex.I‖ = √2 := by
    symm
    apply (sqrt_eq_iff_eq_sq _ _).mpr
    · have : 1 + Complex.mk 0 1 = Complex.mk 1 1 := Complex.ext_iff.mpr (by simp)
      rw [Complex.I,this]
      rw [compl]
      linarith
    · simp
    · simp
lemma mynorm₀ : ‖1 + √3 * Complex.I‖ = √4 := by
    symm
    apply (sqrt_eq_iff_eq_sq _ _).mpr
    · unfold Complex.I
      have : 1 + √3 * Complex.mk 0 1 = Complex.mk 1 √3 := Complex.ext_iff.mpr (by simp)
      rw [this]
      rw [compl]
      have : √3 * √3 = 3 := by simp
      linarith
    · simp
    · simp

theorem calculate_angle₁ : o.oangle !₂[(1:ℝ), 0] !₂[1, 1] = π / (4:ℝ) := by
  rw [calculate_angle']
  simp [Complex.arg]
  rw [mynorm]
  congr
  refine arcsin_eq_of_sin_eq ?_ ?_
  · field_simp
    have : sin (π/4) = 1/√2 := by rw [sin_pi_div_four];simp;grind
    rw [this]
    simp
  · constructor <;> linarith [pi_nonneg]

-- example : Orientation.oangle _ !₂[(1:ℂ), 0] !₂[1, 1] = π / (4:ℝ) := by sorry

theorem calculate_angle₂ :
    (o.oangle !₂[(1:ℝ), 0] !₂[1, √3]) = π / (3:ℝ) := by
  rw [calculate_angle']
  simp [Complex.arg]
  rw [mynorm₀]
  congr
  refine arcsin_eq_of_sin_eq ?_ ?_
  · have : √4 = 2 := by
      refine sqrt_eq_cases.mpr ?_
      left
      simp
      linarith
    field_simp
    rw [sin_pi_div_three]
    field_simp
    tauto
  · constructor <;> linarith [pi_nonneg]


lemma mynorm₁ : √12 = ‖3 + √3 * Complex.I‖  := by
    apply (sqrt_eq_iff_eq_sq (by simp) (by simp)).mpr
    have : 3 + √3 * Complex.mk 0 1 = Complex.mk 3 √3 := Complex.ext_iff.mpr (by simp)
    rw [Complex.I,this,compl]
    have : √3 * √3 = 3 := by simp
    linarith

theorem calculate_angle₃ : o.oangle !₂[(√3:ℝ), 0] !₂[√3, 1] = π / (6:ℝ) := by
  rw [calculate_angle']
  simp [Complex.arg]
  have h₀ : (√3 : ℂ) * √ 3 = 3 := Complex.ext (by simp) (by simp)
  rw [h₀]
  rw [← mynorm₁]
  field_simp
  congr
  refine arcsin_eq_of_sin_eq ?_ ?_
  rw [sin_pi_div_six]
  field_simp
  rw [show (12:ℝ) = 4 * 3 by linarith]
  simp
  refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
  simp
  linarith
  simp
  constructor
  apply le_trans
  show _ ≤ 0
  simp
  positivity
  positivity
  field_simp
  linarith

example  (θ : ℝ) :
    !![cos θ, sin θ;
      -sin θ, cos θ] * !![cos θ, sin θ;
      -sin θ, cos θ] = !![cos (2*θ), sin (2*θ);
      -sin (2*θ), cos (2*θ)] := by
  rw [cos_two_mul, sin_two_mul]
  simp
  rw [← cos_sq_add_sin_sq θ]
  simp
  ring_nf
  simp
  linarith [cos_sq_add_sin_sq θ]

lemma l₀  (θ ψ : ℝ) :
    !![cos θ, sin θ;
      -sin θ, cos θ] * !![cos ψ, sin ψ;
      -sin ψ, cos ψ] = !![cos (θ+ψ), sin (θ+ψ);
      -sin (θ+ψ), cos (θ+ψ)] := by
  rw [cos_add, sin_add]
  simp
  ring_nf
  simp


lemma l₁ {R : Type*} [Ring R] (f : ℝ → R) (h₀ : f 0 = 1)
  (hf : ∀ x y, f (x + y) = f x * f y) (k : ℕ) (y : ℝ) :
  f (k * y) = f y ^ k := by
  induction k with
  | zero => simp;exact h₀
  | succ n ih =>
    rw [pow_succ, ← ih, ← hf]
    congr
    norm_num
    ring_nf

lemma l₂ (θ : ℝ) (k : ℕ) :
    (fun θ => !![cos θ, sin θ;
      -sin θ, cos θ]) (k*θ)
    = (fun θ =>
    !![cos θ, sin θ;
      -sin θ, cos θ]) θ ^ k := by
  have := @l₁ (Matrix (Fin 2) (Fin 2) ℝ) _
    (fun θ => !![cos θ, sin θ;
      -sin θ, cos θ]) (by
        ext i j; fin_cases i <;> fin_cases j <;> simp)
  apply this
  simp
  intro x y
  rw [cos_add]
  rw [sin_add]
  ring_nf
  simp


lemma l₃ (θ : ℝ) (k : ℕ) :
    !![cos (k*θ), sin (k*θ);
      -sin (k*θ), cos (k*θ)] = !![cos θ, sin θ;
                                 -sin θ, cos θ] ^ k := by apply l₂


theorem calculate_angle₅ (θ x y : ℝ) (h : 0 < x^2 + y^2)
    (hθ : θ ∈ Set.Ioc (-π) π) : o.oangle
    !₂[cos θ * x + sin θ * y,
      -sin θ * x + cos θ * y] !₂[x,y]
    = θ := by
    rw [calculate_angle']
    simp
    ring_nf
    have h₀ : Complex.cos ↑θ * ↑x ^ 2 + Complex.cos ↑θ * ↑y ^ 2 + ↑x ^ 2 * Complex.sin ↑θ * Complex.I +
        Complex.sin ↑θ * ↑y ^ 2 * Complex.I =
        (↑x ^ 2 + ↑y ^ 2) * (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I) := by
        ring_nf
    rw [h₀]
    have (r : ℝ) (z : ℂ) (h : 0 < r) : (r * z).arg = z.arg :=
        Complex.arg_real_mul z h
    have h₁ := this (x^2+y^2) (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I) h
    have h₂ : (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I).arg = θ := by
        refine Complex.arg_cos_add_sin_mul_I ?_
        exact hθ
    have := Complex.arg_real_mul (x := (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I))
        (r := x^2+y^2) h
    nth_rewrite 3 [← h₂]
    rw [← this]
    congr
    simp

theorem calculate_angle₆ (θ x y : ℝ) (h : 0 < x^2 + y^2)
    (hθ : θ ∈ Set.Ioc (-π) π) : o.oangle !₂[
    Matrix.mulᵣ !![cos θ, sin θ; -sin θ, cos θ] !![x; y] 0 0,
    Matrix.mulᵣ !![cos θ, sin θ; -sin θ, cos θ] !![x; y] 1 0
    ] !₂[x,y] = θ := by
  rw [← calculate_angle₅ θ x y h hθ]
  congr


theorem calculate_angle₈ (θ x y : ℝ) (h : 0 < x^2 + y^2)
    (hθ : θ ∈ Set.Ioc (-π) π) : o.oangle
    (
        (WithLp.equiv 2 _).symm fun i =>
            Matrix.mulᵣ !![cos θ, sin θ;
                          -sin θ, cos θ]
                        !![x; y]
            i 0
    ) !₂[x,y] = θ := by
  rw [← calculate_angle₅ θ x y h hθ]
  congr
  ext i
  fin_cases i <;> simp



theorem calculate_angle₄ : o.oangle !₂[(1:ℝ), 0] !₂[1, √2-1] = π / (8:ℝ) := by
  rw [calculate_angle']
  simp [Complex.arg]
  have h₀ : ‖1 + (√2 - 1) * Complex.I‖^2 =
        (1^2 + (√2 - 1)^2) := by
        rw [compl];simp;ring_nf
        norm_num
        grind
  have h₁ : ‖1 + (√2 - 1) * Complex.I‖ =
        √(1^2 + (√2 - 1)^2) := by rw [← h₀];simp
  rw [h₁]
  have h₂ : (√2-1)^2 = 2 - 2 * √2 + 1 := by
    ring_nf
    simp
    linarith
  rw [h₂]
  have h₃ : 1^2 + (2 - 2 * √2 + 1)
              = 4 - 2 * √2 := by linarith
  rw [h₃]
  have h₄ : (4 - 2 * √2) = 2 * (2 - √2) := by ring_nf
  rw [h₄]
  have h₅ :  2 * (2 - √2) = 2 * √2 * (√2 - 1) := by
    ring_nf
    simp
    linarith
  rw [h₅]
  have h₆ := sin_pi_div_eight
  have : (√2 - 1) / √(2 * √2 * (√2 - 1))
        =  √(2 - √2) / 2 := by
    suffices (√2 - 1) / √(2 * √2 * (√2 - 1)) * √(2 * √2 * (√2 - 1))
        =  √(2 - √2) / 2 * √(2 * √2 * (√2 - 1)) by
        apply mul_right_cancel₀ (b := √(2 * √2 * (√2 - 1)))
        simp
        intro hc
        have : √2 = 1 := by linarith
        simp at this
        exact this
    rw [div_mul_cancel₀]
    suffices (√2 - 1) * 2 = (√(2 - √2) / 2 * √(2 * √2 * (√2 - 1))) * 2 by
        apply mul_right_cancel₀ (b := 2)
        simp
        exact this
    nth_rewrite 3 [mul_comm]
    rw [mul_assoc]
    rw [div_mul_cancel₀]
    suffices ((√2 - 1) * 2)^2 = (√(2 * √2 * (√2 - 1)) * √(2 - √2))^2 by
        have (x y : ℝ) (h₀ : 0 ≤ x) (h₁ : 0 ≤ y) (h : x^2 = y^2) : x = y := by
            have : x * x - y * y = 0 := by linarith
            have : (x - y) * (x + y) = 0 := by linarith
            have : x - y = 0 ∨ x + y = 0 := mul_eq_zero.mp this
            cases this <;> linarith
        apply this
        · tauto
        · apply mul_nonneg <;> simp
        · apply mul_nonneg <;> simp
    repeat rw [mul_pow]
    repeat rw [sq_sqrt]
    ring_nf
    field_simp
    ring_nf
    have : (√ 2)^3 = √2 * √2 * √2 := by ring_nf
    rw [this]
    simp
    linarith
    simp
    refine sqrt_le_iff.mpr ?_
    simp
    · linarith
    · simp
    · simp
    ·   simp
        intro hc
        have : √ 2 = 1 := by linarith
        simp at this
  rw [this]
  clear this h₅ h₄ h₃ h₂ h₁ h₀
  refine Angle.angle_eq_iff_two_pi_dvd_sub.mpr ?_
  use 0
  simp
  suffices  arcsin (√(2 - √2) / 2) = π / 8 by
    linarith
  have : 0 ≤ π := pi_nonneg
  refine arcsin_eq_of_sin_eq h₆ ?_
  simp
  constructor
  linarith
  linarith


example : ∡ e₁ 0 (WithLp.toLp 2 ![-1,0]) = π := by
  unfold e₁
  rw [Sbtw.oangle₃₂₁_eq_pi (by
    refine sbtw_iff_left_ne_and_right_mem_image_Ioi.mpr ?_
    constructor
    · simp
    · simp
      use 2
      constructor
      · simp
      · unfold AffineMap.lineMap
        simp
        ext i
        fin_cases i
        simp
        linarith
        simp)]
