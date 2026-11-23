import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

theorem slash_periodic_comp {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ}
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) (x : SL(2, ℤ)) :
    Function.Periodic ((f ∣[k] x) ∘ ofComplex) (M : ℝ) := by
  have key : ∀ τ : ℍ, (f ∣[k] x) ((M : ℝ) +ᵥ τ) = (f ∣[k] x) τ := by
    intro τ
    have hT : (ModularGroup.T ^ (M : ℤ)) • τ = (M : ℝ) +ᵥ τ := by
      rw [modular_T_zpow_smul]; simp
    have hδ : x * ModularGroup.T ^ (M : ℤ) * x⁻¹ ∈ Γ := by
      have h1 : ModularGroup.T ^ (M : ℤ) ∈ CongruenceSubgroup.Gamma M := by
        simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (M : ℤ) (M : ℤ) dvd_rfl
      exact hΓ ((CongruenceSubgroup.Gamma_normal M).conj_mem _ h1 x)
    have e : (f ∣[k] x) ∣[k] (ModularGroup.T ^ (M : ℤ)) = f ∣[k] x := by
      rw [← SlashAction.slash_mul,
        (inv_mul_cancel_right (x * ModularGroup.T ^ (M : ℤ)) x).symm,
        SlashAction.slash_mul, hf.1 _ hδ]
    have h := congrFun e τ
    have hden : denom (ModularGroup.T ^ (M : ℤ) : SL(2, ℤ)) τ = 1 := by
      rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
    rw [ModularForm.SL_slash_apply (f := f ∣[k] x), hT, hden, one_zpow, mul_one] at h
    exact h
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simp [hw]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    convert key ⟨w, hw⟩ using 2
    ext
    simp [ofComplex_apply_of_im_pos hw', add_comm]
  · push_neg at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem analyticAt_cuspFunction_slash {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ}
    (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) (x : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction (M : ℝ) (f ∣[k] x)) 0 :=
  analyticAt_cuspFunction_zero (by exact_mod_cast hM) (slash_periodic_comp hΓ hf x)
    (mdiff_slash hf.2.1 k x) (hf.2.2 x)

theorem qParam_one_vadd_eq_exp_mul (M : ℕ) (τ : ℍ) :
    Function.Periodic.qParam (M : ℝ) (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / M) * Function.Periodic.qParam (M : ℝ) (τ : ℂ) := by
  simp only [Function.Periodic.qParam, coe_vadd, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeff_unique_of_hasSum {h : ℝ} {g : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hs : ∀ τ : ℍ, HasSum (fun m => c m • Function.Periodic.qParam h (τ : ℂ) ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

theorem co_transform (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) (hM : 0 < M)
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) :
    (∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (x * ModularGroup.T) n =
        Complex.exp (2 * Real.pi * Complex.I / M) ^ n * co M k f x n) ∧
      (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (γ * x) n = co M k f x n) ∧
      (Odd k → ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (-x) n = -co M k f x n) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨fun x n => ?_, fun γ hγ x n => ?_, fun hk x n => ?_⟩
  · set ζ := Complex.exp (2 * Real.pi * Complex.I / M)
    have happ : ∀ τ : ℍ, (f ∣[k] (x * ModularGroup.T)) τ = (f ∣[k] x) ((1 : ℝ) +ᵥ τ) := by
      intro τ
      rw [slash_mul_apply, modular_T_smul]
      have hden : denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = 1 := by
        rw [ModularGroup.denom_apply]; simp [ModularGroup.T]
      rw [hden, one_zpow, mul_one]
    have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => (ζ ^ m * co M k f x m) •
        Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ m) ((f ∣[k] (x * ModularGroup.T)) τ) := by
      intro τ
      have h := hasSum_qExpansion hM' (slash_periodic_comp hΓ hf x) (mdiff_slash hf.2.1 k x)
        (hf.2.2 x) ((1 : ℝ) +ᵥ τ)
      rw [happ]
      convert h using 1
      funext m
      rw [qParam_one_vadd_eq_exp_mul, co, smul_eq_mul, smul_eq_mul, mul_pow]
      ring
    exact (coeff_unique_of_hasSum hM'
      (analyticAt_cuspFunction_slash hM hΓ hf (x * ModularGroup.T)) hsum n).symm
  · simp only [co, hf.slash_mul hγ x]
  · simp only [co, slash_neg_of_odd hk f x]
    rw [qExpansion_neg (analyticAt_cuspFunction_slash hM hΓ hf x)]
    simp

end GlobalTheory.OddFrame
