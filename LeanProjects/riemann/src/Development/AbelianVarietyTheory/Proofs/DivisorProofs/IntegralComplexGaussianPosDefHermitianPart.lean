import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.MatrixGaussian

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_congr_diagonal (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    ∃ (M : Matrix ι ι ℂ) (d : ι → ℂ), M.det ≠ 0 ∧ (∀ i, 0 < (d i).re) ∧ Mᴴ * A * M = diagonal d := by
  obtain ⟨B, hB, hBA⟩ : ∃ B : Matrix ι ι ℂ, IsUnit B ∧ A + Aᴴ = star B * B := by
    open scoped MatrixOrder in
    exact CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  set C := B⁻¹ with hC
  have h1 : B * C = 1 := Matrix.mul_nonsing_inv B hBd
  set A' := Cᴴ * A * C with hA'
  have h2 : A' + A'ᴴ = 1 := by
    have : A' + A'ᴴ = Cᴴ * (A + Aᴴ) * C := by
      simp only [hA', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_assoc]
    rw [this, hBA, star_eq_conjTranspose]
    calc Cᴴ * (Bᴴ * B) * C = (B * C)ᴴ * (B * C) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp
  have hK : (I • (A' - A'ᴴ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    simp only [RCLike.star_def, conj_I, neg_smul, ← smul_neg, neg_sub]
  set U : Matrix ι ι ℂ := (hK.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : Uᴴ * U = 1 := hK.eigenvectorUnitary.2.1
  have hD : Uᴴ * (I • (A' - A'ᴴ)) * U = diagonal (RCLike.ofReal ∘ hK.eigenvalues) := by
    have := hK.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using this
  have h3 : A' = (1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ))) := by
    rw [← h2, smul_smul, I_mul_I]
    module
  refine ⟨C * U, fun i => (1 / 2 : ℂ) * (1 - I * (hK.eigenvalues i : ℂ)), ?_, fun i => by simp, ?_⟩
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · intro h
      have := congrArg det h1
      simp [h] at this
    · intro h
      have := congrArg det hUU
      simp [h] at this
  · calc (C * U)ᴴ * A * (C * U) = Uᴴ * A' * U := by
          simp only [hA', conjTranspose_mul, Matrix.mul_assoc]
      _ = Uᴴ * ((1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ)))) * U := by rw [← h3]
      _ = (1 / 2 : ℂ) • (Uᴴ * U - I • (Uᴴ * (I • (A' - A'ᴴ)) * U)) := by
          generalize I • (A' - A'ᴴ) = K
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = _ := by
          rw [hD, hUU]
          ext i j
          by_cases h : i = j
          · subst h; simp
          · simp [h]

theorem exp_diagonal (d z : ι → ℂ) :
    cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = ∏ i, cexp (-(π * d i) * (‖z i‖ : ℂ) ^ 2) := by
  rw [← Complex.exp_sum, dotProduct, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, ← Complex.conj_mul', Pi.star_apply, RCLike.star_def]
  ring

theorem gaussian_diagonal (d : ι → ℂ) (hd : ∀ i, 0 < (d i).re) :
    Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = (diagonal d).det⁻¹ := by
  have hb : ∀ i, 0 < ((π : ℂ) * d i).re := fun i => by
    simpa using mul_pos Real.pi_pos (hd i)
  simp only [exp_diagonal]
  constructor
  · refine Integrable.fintype_prod (f := fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)) fun i => ?_
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (hb i) 0 0
  · rw [integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)),
      det_diagonal, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (hb i), Complex.finrank_real_complex]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
    rw [this, cpow_one, div_mul_cancel_left₀ hπ]

theorem map_mulVec_volume (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    Measure.map (fun z : ι → ℂ => M *ᵥ z) volume = ENNReal.ofReal (normSq M.det)⁻¹ • volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = normSq M.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; simpa using hM)
  rw [hdet, abs_of_nonneg (inv_nonneg.2 (normSq_nonneg _))] at this
  exact this

theorem integral_gaussian (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  obtain ⟨M, d, hM, hd, hMA⟩ := exists_congr_diagonal A hA
  obtain ⟨hi, he⟩ := gaussian_diagonal d hd
  have hn : 0 < normSq M.det := normSq_pos.2 hM
  have hdet : (diagonal d).det = (normSq M.det : ℂ) * A.det := by
    rw [← hMA, det_mul, det_mul, det_conjTranspose, normSq_eq_conj_mul_self, RCLike.star_def]
    ring
  have hd0 : (diagonal d).det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ h => ?_
    have := hd i
    simp [h] at this
  have hA0 : A.det ≠ 0 := fun h => hd0 (by rw [hdet, h, mul_zero])
  have hcomp : ∀ z : ι → ℂ, star (M *ᵥ z) ⬝ᵥ A *ᵥ (M *ᵥ z) = star z ⬝ᵥ (diagonal d) *ᵥ z := fun z => by
    rw [← hMA, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hc : Continuous fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) := by fun_prop
  have hcM : Continuous fun z : ι → ℂ => M *ᵥ z := by fun_prop
  have hmap := map_mulVec_volume M hM
  refine ⟨hA0, ?_, ?_⟩
  · have h := (integrable_map_measure (μ := volume) hc.aestronglyMeasurable hcM.measurable.aemeasurable).2
      (by simpa only [Function.comp_def, hcomp] using hi)
    rw [hmap] at h
    exact (integrable_smul_measure (by simpa using hn) ENNReal.ofReal_ne_top).1 h
  · have h := integral_map (μ := volume) hcM.measurable.aemeasurable hc.aestronglyMeasurable
    simp only [hcomp] at h
    rw [hmap, integral_smul_measure, he, hdet, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le), real_smul,
      mul_inv, ofReal_inv] at h
    exact mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast hn.ne')) h

end GlobalTheory.MatrixGaussian
