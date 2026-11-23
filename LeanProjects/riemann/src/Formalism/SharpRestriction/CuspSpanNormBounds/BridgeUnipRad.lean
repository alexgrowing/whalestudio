import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuspidalRangeOfReproUnipotent

noncomputable section

namespace Formalism.MainNotions.BridgeUnipRad

open MeasureTheory NumberField Matrix
open Formalism.MainNotions.S

section CM

variable (I : AutInst)

theorem emb_star (v : InfinitePlace I.F) (x : I.E) : I.φ v (star x) = starRingEnd ℂ (I.φ v x) := by
  obtain ⟨hcm, -, -, -⟩ := I.cm
  unfold Formalism.HermitianLatticesTheory.IsCMUnram at hcm
  exact hcm.2.1 (I.φ v) x

end CM

section Form

variable {n : ℕ}

theorem hform_eq (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  rw [Formalism.UG.hform.eq_1]
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

end Form

section Span

variable (I : AutInst)

def WC (v : InfinitePlace I.F) (W : Submodule I.E (Fin I.n → I.E)) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set (Fin I.n → I.E)))

end Span

section Rad

variable {n : ℕ}

def UPerp (J' : Matrix (Fin n) (Fin n) ℂ) (U : Submodule ℂ (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {y | ∀ x ∈ U, Formalism.UG.hform (starRingEnd ℂ) J' x y = 0}

def URad (J' : Matrix (Fin n) (Fin n) ℂ) (U : Submodule ℂ (Fin n → ℂ)) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ x ∈ U, (g - 1) *ᵥ x = 0) ∧ (∀ y ∈ UPerp J' U, (g - 1) *ᵥ y ∈ U) ∧ ∀ y, (g - 1) *ᵥ y ∈ UPerp J' U

variable {J' : Matrix (Fin n) (Fin n) ℂ} {U : Submodule ℂ (Fin n → ℂ)}

theorem uperp_add {y y' : Fin n → ℂ} (hy : y ∈ UPerp J' U) (hy' : y' ∈ UPerp J' U) : y + y' ∈ UPerp J' U := by
  simp only [UPerp, Set.mem_setOf_eq] at hy hy' ⊢
  intro x hx
  have h1 := hy x hx
  have h2 := hy' x hx
  rw [hform_eq] at h1 h2 ⊢
  rw [mulVec_add, dotProduct_add, h1, h2, add_zero]

theorem uperp_neg {y : Fin n → ℂ} (hy : y ∈ UPerp J' U) : -y ∈ UPerp J' U := by
  simp only [UPerp, Set.mem_setOf_eq] at hy ⊢
  intro x hx
  have h1 := hy x hx
  rw [hform_eq] at h1 ⊢
  rw [mulVec_neg, dotProduct_neg, h1, neg_zero]

theorem uperp_zero : (0 : Fin n → ℂ) ∈ UPerp J' U := by
  simp only [UPerp, Set.mem_setOf_eq]
  intro x _
  rw [hform_eq, mulVec_zero, dotProduct_zero]

theorem urad_one : URad J' U 1 := by
  unfold URad
  refine ⟨fun x _ => by simp, fun y _ => by simp, fun y => ?_⟩
  simpa using (uperp_zero : (0 : Fin n → ℂ) ∈ UPerp J' U)

theorem urad_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hA : URad J' U A) (hB : URad J' U B) : URad J' U (A * B) := by
  unfold URad at hA hB ⊢
  obtain ⟨a1, a2, a3⟩ := hA
  obtain ⟨b1, b2, b3⟩ := hB
  have key : ∀ v, (A * B - 1) *ᵥ v = (A - 1) *ᵥ v + (A - 1) *ᵥ ((B - 1) *ᵥ v) + (B - 1) *ᵥ v := by
    intro v
    simp only [sub_mulVec, one_mulVec, mulVec_sub, ← mulVec_mulVec]
    abel
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y => ?_⟩
  · rw [key, a1 x hx, b1 x hx, mulVec_zero, add_zero, add_zero]
  · rw [key, a1 _ (b2 y hy), add_zero]
    exact U.add_mem (a2 y hy) (b2 y hy)
  · rw [key]
    exact uperp_add (uperp_add (a3 y) (a3 _)) (b3 y)

theorem urad_inv {A A' : Matrix (Fin n) (Fin n) ℂ} (hA : URad J' U A) (h1 : A' * A = 1) (h2 : A * A' = 1)
    (hu : ∀ a b, Formalism.UG.hform (starRingEnd ℂ) J' (A *ᵥ a) (A *ᵥ b) = Formalism.UG.hform (starRingEnd ℂ) J' a b) :
    URad J' U A' := by
  unfold URad at hA ⊢
  obtain ⟨a1, a2, a3⟩ := hA
  have key : ∀ v, (A' - 1) *ᵥ v = -(A' *ᵥ ((A - 1) *ᵥ v)) := by
    intro v
    simp only [sub_mulVec, one_mulVec, mulVec_sub, mulVec_mulVec, h1]
    abel
  have fixA : ∀ x ∈ U, A *ᵥ x = x := by
    intro x hx
    have := a1 x hx
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at this
    exact this
  have hA'A : ∀ z, A' *ᵥ (A *ᵥ z) = z := by
    intro z
    rw [mulVec_mulVec, h1, one_mulVec]
  have hAA' : ∀ z, A *ᵥ (A' *ᵥ z) = z := by
    intro z
    rw [mulVec_mulVec, h2, one_mulVec]
  have fixU : ∀ x ∈ U, A' *ᵥ x = x := by
    intro x hx
    conv_lhs => rw [← fixA x hx]
    exact hA'A x
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y => ?_⟩
  · rw [sub_mulVec, one_mulVec, fixU x hx, sub_self]
  · rw [key, fixU _ (a2 y hy)]
    exact U.neg_mem (a2 y hy)
  · rw [key]
    apply uperp_neg
    have hz := a3 y
    simp only [UPerp, Set.mem_setOf_eq] at hz ⊢
    intro x hx
    rw [← hu x (A' *ᵥ ((A - 1) *ᵥ y)), fixA x hx, hAA']
    exact hz x hx

end Rad

section Sub

variable {n : ℕ} (ε : Fin n → Bool) {P J' : Matrix (Fin n) (Fin n) ℂ}

theorem conj_mat_mul (hP : IsUnit P) (g h : Formalism.REAL.UJ ε) :
    P * uMat (g * h) * P⁻¹ = (P * uMat g * P⁻¹) * (P * uMat h * P⁻¹) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hm : uMat (g * h) = uMat g * uMat h := by first | rfl | simp [uMat]
  rw [hm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]

theorem conj_mat_one (hP : IsUnit P) : P * uMat (1 : Formalism.REAL.UJ ε) * P⁻¹ = 1 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : uMat (1 : Formalism.REAL.UJ ε) = 1 := by first | rfl | simp [uMat]
  rw [h1, Matrix.mul_one, Matrix.mul_nonsing_inv P hd]

theorem conj_mat_unitary (hP : IsUnit P) (hJ : Pᴴ * J' * P = Formalism.REAL.Jm ε) (g : Formalism.REAL.UJ ε) (a b : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) J' ((P * uMat g * P⁻¹) *ᵥ a) ((P * uMat g * P⁻¹) *ᵥ b) =
      Formalism.UG.hform (starRingEnd ℂ) J' a b := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hPiH : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := by
    first
      | exact g.2
      | (have h := g.prop; rw [Formalism.REAL.UJ.eq_1] at h; exact h)
  set Q := P * uMat g * P⁻¹ with hQdef
  have hQ : Qᴴ * J' * Q = J' := by
    rw [hQdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc (P⁻¹)ᴴ * ((uMat g)ᴴ * Pᴴ) * J' * (P * uMat g * P⁻¹)
        = (P⁻¹)ᴴ * ((uMat g)ᴴ * (Pᴴ * J' * P) * uMat g) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * J' * P) * P⁻¹ := by rw [hJ, hg]
      _ = ((P⁻¹)ᴴ * Pᴴ) * J' * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J' := by rw [hPiH, hPi, Matrix.one_mul, Matrix.mul_one]
  simp only [hform_eq, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hQ]

def NSub (hP : IsUnit P) (hJ : Pᴴ * J' * P = Formalism.REAL.Jm ε) (U : Submodule ℂ (Fin n → ℂ)) :
    Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | URad J' U (P * uMat g * P⁻¹)}
  one_mem' := by
    show URad J' U (P * uMat (1 : Formalism.REAL.UJ ε) * P⁻¹)
    rw [conj_mat_one ε hP]
    exact urad_one
  mul_mem' := by
    intro g h hg hh
    show URad J' U (P * uMat (g * h) * P⁻¹)
    rw [conj_mat_mul ε hP]
    exact urad_mul hg hh
  inv_mem' := by
    intro g hg
    show URad J' U (P * uMat g⁻¹ * P⁻¹)
    refine urad_inv hg ?_ ?_ (conj_mat_unitary ε hP hJ g)
    · rw [← conj_mat_mul ε hP, inv_mul_cancel, conj_mat_one ε hP]
    · rw [← conj_mat_mul ε hP, mul_inv_cancel, conj_mat_one ε hP]

end Sub

def HCCusp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ u w : H, u ∈ lowKSub ε lam σ → w ∈ lowKSub ε lam σ →
    ∀ P J' : Matrix (Fin n) (Fin n) ℂ, IsUnit P → Pᴴ * J' * P = Formalism.REAL.Jm ε →
    ∀ U : Submodule ℂ (Fin n → ℂ), U ≠ ⊥ → (∀ x ∈ U, ∀ y ∈ U, Formalism.UG.hform (starRingEnd ℂ) J' x y = 0) →
    ∀ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = {g | URad J' U (P * uMat g * P⁻¹)} →
    ∀ ν : Measure N, ν.IsHaarMeasure →
    ∀ x y : Formalism.REAL.UJ ε, ∫ m, coefOn σ u w (x * (m : Formalism.REAL.UJ ε) * y) ∂ν = 0

def URadUnimod : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P J' : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * J' * P = Formalism.REAL.Jm ε →
    ∀ U : Submodule ℂ (Fin n → ℂ), U ≠ ⊥ → (∀ x ∈ U, ∀ y ∈ U, Formalism.UG.hform (starRingEnd ℂ) J' x y = 0) →
    ∀ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = {g | URad J' U (P * uMat g * P⁻¹)} →
    ∀ ν : Measure N, ν.IsHaarMeasure → ν.IsMulRightInvariant

end Formalism.MainNotions.BridgeUnipRad

end
