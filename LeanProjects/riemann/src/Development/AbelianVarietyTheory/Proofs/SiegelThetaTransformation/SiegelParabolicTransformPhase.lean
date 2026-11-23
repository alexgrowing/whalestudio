import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationSiegelParabolic

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.ParabValues

open GlobalTheory.SW.Parab

theorem ph_rat_mul_exp (r q : ℚ) : Ph ((r : ℂ) * cexp (-(Real.pi * I * (q : ℂ)))) := by
  refine ⟨2 * q.den, by have := q.den_pos; omega, ?_⟩
  have hn : ‖cexp (-(Real.pi * I * (q : ℂ)))‖ = 1 := by
    have : -(Real.pi * I * (q : ℂ)) = ((-(Real.pi * q) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have he : cexp (-(Real.pi * I * (q : ℂ))) ^ (2 * q.den) = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨-q.num, ?_⟩
    have h : (q : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num q
    push_cast
    rw [← h]
    ring
  rw [mul_pow, he, mul_one, norm_mul, hn, mul_one, Complex.norm_ratCast]
  have : (|(r : ℝ)|) ^ (2 * q.den) = (r : ℝ) ^ (2 * q.den) := Even.pow_abs ⟨q.den, by ring⟩ _
  rw [← Complex.ofReal_pow, this]
  push_cast
  rfl

theorem trans_explicit (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hC : σ.toBlocks₂₁ = 0)
    (φ : Matrix κ ι ℚ → ℂ) (hφ : IsSB φ) :
    IsSB (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) ∧
    TransS σ φ (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) := by
  classical
  set A := σ.toBlocks₁₁ with hA
  set B := σ.toBlocks₁₂ with hB
  set D := σ.toBlocks₂₂ with hD
  have hDA : D * Aᵀ = 1 := by
    have h := SymplecticGroup.mem_iff.mp hσ
    rw [← Matrix.fromBlocks_toBlocks σ, hC, Matrix.J, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
    have := congrArg Matrix.toBlocks₂₁ h
    simpa using this
  have hdet : D.det * A.det = 1 := by
    have := congrArg Matrix.det hDA
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hA0 : A.det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA0
  refine ⟨?_, ?_⟩
  · have h1 := isSB_parChar_mul (B * Aᵀ) _
      ((GlobalTheory.SW.LinChange.haar_mul ℚ κ ι φ hφ).1 A hA0).1
    exact (GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ h1 h1).2.1 _
  · intro τ _ ζ
    have hden : spDen σ τ = qm D := by
      unfold spDen
      rw [hC]
      have : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
      rw [this, Matrix.zero_mul, zero_add]
    have hinv : (qm D)⁻¹ = (qm A)ᵀ := by
      apply Matrix.inv_eq_right_inv
      have e : (qm A)ᵀ = qm Aᵀ := rfl
      rw [e, ← qm_mul', hDA]
      ext i j; by_cases h : i = j <;> simp [qm, Matrix.one_apply, h]
    have hdetD : (qm D).det = (D.det : ℂ) := ((Rat.castHom ℂ).map_det D).symm
    have hC' : qm σ.toBlocks₂₁ = 0 := by rw [hC]; ext i j; simp [qm]
    unfold spAct
    rw [hden, hinv, hC', hdetD]
    simp only [Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero, Finset.sum_const_zero,
      mul_zero, Complex.exp_zero, mul_one]
    let e : Matrix κ ι ℚ ≃ Matrix κ ι ℚ :=
      { toFun := fun x => x * A
        invFun := fun x => x * A⁻¹
        left_inv := fun x => Matrix.mul_nonsing_inv_cancel_right A x hAu
        right_inv := fun x => Matrix.nonsing_inv_mul_cancel_right A x hAu }
    unfold thS
    rw [← tsum_mul_left, ← e.tsum_eq (fun x => _ * (φ x * _))]
    refine tsum_congr fun x => ?_
    show ((D.det : ℂ) ^ (Fintype.card κ / 2)) * (parChar (B * Aᵀ) x * φ (x * A)) * _ =
      _ * (φ (x * A) * cexp (Real.pi * I * ∑ k, (qv ((x * A) k) ⬝ᵥ τ *ᵥ qv ((x * A) k) +
        2 * (qv ((x * A) k) ⬝ᵥ ζ k))))
    rw [mul_assoc, mul_comm (parChar _ _), mul_assoc]
    congr 2
    unfold parChar
    rw [← Complex.exp_add]
    congr 1
    rw [← mul_neg, ← mul_add, Rat.cast_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [qv_bilin, qv_row_mul, qm_mul']
    have e1 : qm Aᵀ = (qm A)ᵀ := rfl
    beta_reduce
    rw [e1, Matrix.add_mul, Matrix.add_mulVec, dotProduct_add, Matrix.vecMul_transpose,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_transpose, Matrix.dotProduct_mulVec (qv (x k)) (qm A),
      Matrix.dotProduct_mulVec (qv (x k)) (qm A)]
    ring

theorem trans_unique (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    (φ ψ ψ' : Matrix κ ι ℚ → ℂ) (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e : ζ = fun k => (ζ k ᵥ* spDen σ (I • (1 : Matrix ι ι ℂ))) ᵥ*
      (spDen σ (I • (1 : Matrix ι ι ℂ)))⁻¹ := by
    funext k
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.vecMul_one]
  rw [e, h _ I_mem_siegel, h' _ I_mem_siegel]

theorem values_parabolic : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, σ.toBlocks₂₁ = 0 → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ → TransS σ φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ), Ph u ∧ ψ y = u * φ y' := by
  intro κ ι _ _ _ _ σ hσ hC φ ψ hφ hψ h y
  obtain ⟨h1, h2⟩ := trans_explicit κ ι σ hσ hC φ hφ
  have e := trans_unique κ ι σ hσ φ _ _ hψ h1 h h2
  refine ⟨((σ.toBlocks₂₂.det ^ (Fintype.card κ / 2) : ℚ) : ℂ) *
    parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) y, y * σ.toBlocks₁₁, ph_rat_mul_exp _ _, ?_⟩
  rw [e]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end GlobalTheory.Phase.ParabValues
