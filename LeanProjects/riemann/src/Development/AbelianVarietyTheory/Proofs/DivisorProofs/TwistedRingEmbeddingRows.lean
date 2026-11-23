import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

noncomputable section

namespace GlobalTheory.ThK.PlaneCo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem planeCoef_mul_planeMat_ne {n n₁ : ℕ} (H : Plane E n n₁) {k j : Fin n₁ ⊕ Fin 2} (hkj : k ≠ j) :
    (planeCoef H * planeMat H) k j = 0 := by
  unfold planeCoef
  split_ifs with h
  · set e := finSumFinEquiv.trans (finCongr h)
    set A := (planeMat H).submatrix id e.symm
    have hk : (A⁻¹.submatrix e id * planeMat H) k j = (A⁻¹ * A) (e k) (e j) := by
      simp [Matrix.mul_apply, A]
    rw [hk]
    by_cases hA : IsUnit A.det
    · rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_apply_ne (e.injective.ne hkj)]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hA, zero_mul, Matrix.zero_apply]
  · simp

theorem planeCoef_mulVec_x_ne {n n₁ : ℕ} (H : Plane E n n₁) {k : Fin n₁ ⊕ Fin 2} (hk : k ≠ .inr 0) :
    (planeCoef H *ᵥ H.x) k = 0 := by
  have := planeCoef_mul_planeMat_ne H hk
  rw [Matrix.mul_apply] at this
  simpa [Matrix.mulVec, dotProduct, planeMat] using this

theorem planeCoef_mul_ι_inr {n n₁ : ℕ} (H : Plane E n n₁) (t : Fin 2) (j : Fin n₁) :
    (planeCoef H * H.ι) (.inr t) j = 0 := by
  have := planeCoef_mul_planeMat_ne H (k := .inr t) (j := .inl j) (by simp)
  rw [Matrix.mul_apply] at this
  simpa [Matrix.mul_apply, planeMat] using this

theorem coefLin_vecMulVec {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (a : Fin n → AE F E)
    (b : Fin d → AE F E) (k : Fin n₁ ⊕ Fin 2) (l : Fin d₁ ⊕ Fin 2) :
    coefLin H H' (Matrix.vecMulVec a b) k l =
      (incM F (planeCoef H) *ᵥ a) k * (incM F (planeCoef H') *ᵥ b) l := by
  simp only [coefLin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem incM_mulVec_incV_x_ne {n n₁ : ℕ} (H : Plane E n n₁) {k : Fin n₁ ⊕ Fin 2} (hk : k ≠ .inr 0) :
    (incM F (planeCoef H) *ᵥ incV F H.x) k = 0 := by
  have h := planeCoef_mulVec_x_ne H hk
  have := RingHom.map_mulVec (inclR (F := F) (AF F)) (planeCoef H) H.x k
  rw [h, map_zero] at this
  rw [this]; rfl

theorem incM_mulVec_ι_inr {n n₁ : ℕ} (H : Plane E n n₁) (y : Fin n₁ → AE F E) (t : Fin 2) :
    (incM F (planeCoef H) *ᵥ (incM F H.ι *ᵥ y)) (.inr t) = 0 := by
  rw [Matrix.mulVec_mulVec]
  have hm : incM F (planeCoef H) * incM F H.ι = incM F (planeCoef H * H.ι) := by
    simp [incM, Matrix.map_mul]
  rw [hm]
  simp [Matrix.mulVec, dotProduct, incM, planeCoef_mul_ι_inr]

theorem isoB_planeT : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ u ∈ isoB H H',
    (planeT σ X W H H' u).1.1 = 0 ∧ (planeT σ X W H H' u).2 = 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' _ _ _ _ _ u hu
  have hS : ∀ k, sI H H' u k = 0 := by
    intro k
    rcases hu with ⟨z, rfl⟩ | ⟨y, rfl⟩
    · rcases k with j | a
      · simp only [sI, posS, coefLin_vecMulVec]
        rw [incM_mulVec_incV_x_ne H (by simp), zero_mul]
      · simp only [sI, posS, coefLin_vecMulVec]
        rw [incM_mulVec_incV_x_ne H (by simp), zero_mul]
    · rcases k with j | a
      · simp only [sI, posS, coefLin_vecMulVec]
        rw [incM_mulVec_ι_inr, zero_mul]
      · simp only [sI, posS, coefLin_vecMulVec]
        rw [incM_mulVec_incV_x_ne H' (by simp), mul_zero]
  refine ⟨?_, ?_⟩
  · funext k
    simp [planeT, hS]
  · ext i j
    rcases hu with ⟨z, rfl⟩ | ⟨y, rfl⟩
    · simp only [planeT, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply, coefLin_vecMulVec, Matrix.zero_apply]
      rw [incM_mulVec_incV_x_ne H (by simp), zero_mul]
    · simp only [planeT, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply, coefLin_vecMulVec, Matrix.zero_apply]
      rw [incM_mulVec_incV_x_ne H' (by simp), mul_zero]

end GlobalTheory.ThK.PlaneCo
