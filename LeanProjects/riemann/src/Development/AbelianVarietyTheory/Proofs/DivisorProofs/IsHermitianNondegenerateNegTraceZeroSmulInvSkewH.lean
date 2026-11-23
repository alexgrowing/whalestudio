import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory

theorem skew_dual_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = -J i j) → IsUnit J.det → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
    IsHermND σ (-ξ₀ • J⁻¹) := by
  intro F E _ _ _ _ _ σ d J hJ hdet ξ₀ hξ hσξ
  have hinv : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  have hmap : (J⁻¹).map σ * J.map σ = 1 := by
    have := congrArg (fun M => M.map σ) hinv
    simpa [Matrix.map_mul, Matrix.map_one] using this
  have hT : (J.map σ)ᵀ = -J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have h2 : (-J) * ((J⁻¹).map σ)ᵀ = 1 := by
    rw [← hT, ← Matrix.transpose_mul, hmap, Matrix.transpose_one]
  have hX : ((J⁻¹).map σ)ᵀ = -J⁻¹ := by
    have h3 : J * (-((J⁻¹).map σ)ᵀ) = 1 := by
      rw [Matrix.mul_neg, ← Matrix.neg_mul]; exact h2
    have h4 := Matrix.inv_eq_right_inv h3
    have h5 := congrArg Neg.neg h4
    rw [neg_neg] at h5
    exact h5.symm
  have hent : ∀ i j, σ (J⁻¹ j i) = -J⁻¹ i j := by
    intro i j
    have := congrFun (congrFun hX i) j
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_neg, hσξ, hent]
    ring
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hξ)) (Matrix.isUnit_nonsing_inv_det J hdet).ne_zero

end GlobalTheory
