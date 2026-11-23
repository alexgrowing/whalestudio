import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import ReciprocityTheory.DualLattices.HasSumNormalizedDeriv

open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups Function Filter EisensteinSeries
open scoped Real Manifold Topology ModularForm

namespace GlobalTheory.EisWronskian

local notation "𝕢" => Periodic.qParam
local notation "D" => Derivative.normalizedDerivOfComplex

private lemma qParam_add_one (z : ℂ) : 𝕢 1 (z + 1) = 𝕢 1 z := by
  simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one, Complex.exp_add,
    Complex.exp_two_pi_mul_I]

private def Good (G : ℍ → ℂ) : Prop :=
  Periodic (G ∘ ofComplex) 1 ∧ MDiff G ∧ IsBoundedAtImInfty G

private lemma good_of_hasSum {G : ℍ → ℂ} {c : ℕ → ℂ}
    (hG : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 1 τ ^ m) (G τ)) (hol : MDiff G) : Good G := by
  refine ⟨?_, hol, isBoundedAtImInfty_of_hasSum_qExpansion one_pos hG⟩
  intro w
  by_cases hw : 0 < im w
  · have h1 : 0 < im (w + 1) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos h1, ofComplex_apply_of_im_pos hw]
    refine (hG ⟨w + 1, h1⟩).unique ?_
    have := hG ⟨w, hw⟩
    simpa [qParam_add_one] using this
  · have h1 : im (w + 1) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos h1, ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

private lemma Good.mul {G H : ℍ → ℂ} (hG : Good G) (hH : Good H) : Good (G * H) :=
  ⟨hG.1.mul hH.1, hG.2.1.mul hH.2.1, hG.2.2.mul hH.2.2⟩

private lemma Good.smul {G : ℍ → ℂ} (hG : Good G) (a : ℂ) : Good (a • G) :=
  ⟨hG.1.smul a, hG.2.1.const_smul a, hG.2.2.smul a⟩

private lemma Good.sub {G H : ℍ → ℂ} (hG : Good G) (hH : Good H) : Good (G - H) :=
  ⟨hG.1.sub hH.1, hG.2.1.sub hH.2.1, hG.2.2.sub hH.2.2⟩

private lemma Good.analytic {G : ℍ → ℂ} (hG : Good G) : AnalyticAt ℂ (cuspFunction 1 G) 0 :=
  analyticAt_cuspFunction_zero one_pos hG.1 hG.2.1 hG.2.2

private lemma hasSum_f {w : ℤ} (f : ModularForm 𝒮ℒ w) (τ : ℍ) :
    HasSum (fun m ↦ (qExpansion 1 f).coeff m • 𝕢 1 τ ^ m) (f τ) := by
  have : Fact (IsCusp OnePoint.infty 𝒮ℒ) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods_SL⟩
  simpa [smul_eq_mul] using
    UpperHalfPlane.hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

private lemma hasSum_Df {w : ℤ} (f : ModularForm 𝒮ℒ w) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ ((m : ℂ) * (qExpansion 1 f).coeff m) • 𝕢 1 τ ^ m) (D f τ) :=
  ReciprocityTheory.PGsh.hasSum_normalizedDeriv (hasSum_f f) τ

private lemma good_f {w : ℤ} (f : ModularForm 𝒮ℒ w) : Good f :=
  good_of_hasSum (hasSum_f f) (ModularFormClass.holo f)

private lemma good_Df {w : ℤ} (f : ModularForm 𝒮ℒ w) : Good (D f) :=
  good_of_hasSum (hasSum_Df f)
    (Derivative.normalizedDerivOfComplex_mdifferentiable (ModularFormClass.holo f))

private lemma coeff_of_hasSum {G : ℍ → ℂ} {c : ℕ → ℂ} (hG : Good G)
    (hs : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 1 τ ^ m) (G τ)) (m : ℕ) :
    (qExpansion 1 G).coeff m = c m := by
  have h1 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction one_pos hG.analytic
    hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction 1 G)
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (qExpansion 1 G).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hG.analytic.hasFPowerSeriesAt
  have := congr_arg (fun p ↦ FormalMultilinearSeries.coeff p m) (h1.eq_formalMultilinearSeries h2)
  simpa [FormalMultilinearSeries.coeff_ofScalars] using this.symm

private lemma coeff_Df {w : ℤ} (f : ModularForm 𝒮ℒ w) (m : ℕ) :
    (qExpansion 1 (D f)).coeff m = (m : ℂ) * (qExpansion 1 f).coeff m :=
  coeff_of_hasSum (good_Df f) (hasSum_Df f) m

private noncomputable def wr : ℍ → ℂ :=
  (2 : ℂ) • (⇑E₄ * D E₆) - (3 : ℂ) • (⇑E₆ * D E₄)

private lemma good_wr : Good wr :=
  (((good_f E₄).mul (good_Df E₆)).smul _).sub (((good_f E₆).mul (good_Df E₄)).smul _)

private lemma wr_eq : wr = (2 : ℂ) • (⇑E₄ * Derivative.serreDerivative ((6 : ℤ) : ℂ) E₆) -
    (3 : ℂ) • (⇑E₆ * Derivative.serreDerivative ((4 : ℤ) : ℂ) E₄) := by
  ext z
  simp only [wr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    Derivative.serreDerivative_apply]
  push_cast
  ring

private lemma wr_slash (γ : SL(2, ℤ)) : wr ∣[(12 : ℤ)] γ = wr := by
  have h4 : (⇑E₄) ∣[(4 : ℤ)] γ = ⇑E₄ := E₄.slash_action_eq' _ ⟨γ, rfl⟩
  have h6 : (⇑E₆) ∣[(6 : ℤ)] γ = ⇑E₆ := E₆.slash_action_eq' _ ⟨γ, rfl⟩
  have s4 := Derivative.serreDerivative_slash_equivariant (k := 4) (γ := γ)
    (ModularFormClass.holo E₄)
  have s6 := Derivative.serreDerivative_slash_equivariant (k := 6) (γ := γ)
    (ModularFormClass.holo E₆)
  rw [h4] at s4
  rw [h6] at s6
  have m1 := ModularForm.mul_slash_SL2 4 (6 + 2) γ (⇑E₄)
    (Derivative.serreDerivative ((6 : ℤ) : ℂ) E₆)
  have m2 := ModularForm.mul_slash_SL2 6 (4 + 2) γ (⇑E₆)
    (Derivative.serreDerivative ((4 : ℤ) : ℂ) E₄)
  rw [h4, s6, show (4 + (6 + 2) : ℤ) = 12 by norm_num] at m1
  rw [h6, s4, show (6 + (4 + 2) : ℤ) = 12 by norm_num] at m2
  rw [wr_eq, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    ModularForm.SL_smul_slash, ModularForm.SL_smul_slash, m1, m2]

private noncomputable def wrForm : ModularForm 𝒮ℒ 12 where
  toFun := wr
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact wr_slash A
  holo' := good_wr.2.1
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [wr_slash γ]
    exact good_wr.2.2

private lemma qExp_wr : qExpansion 1 wr =
    (2 : ℂ) • (qExpansion 1 E₄ * qExpansion 1 (D E₆)) -
      (3 : ℂ) • (qExpansion 1 E₆ * qExpansion 1 (D E₄)) := by
  have h1 := (good_f E₄).mul (good_Df E₆)
  have h2 := (good_f E₆).mul (good_Df E₄)
  rw [wr, UpperHalfPlane.qExpansion_sub (h1.smul _).analytic (h2.smul _).analytic,
    UpperHalfPlane.qExpansion_smul h1.analytic, UpperHalfPlane.qExpansion_smul h2.analytic,
    UpperHalfPlane.qExpansion_mul (good_f E₄).analytic (good_Df E₆).analytic,
    UpperHalfPlane.qExpansion_mul (good_f E₆).analytic (good_Df E₄).analytic]

private lemma coeff_wr_zero : (qExpansion 1 wr).coeff 0 = 0 := by
  rw [qExp_wr]
  simp [PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff, coeff_Df]

private lemma coeff_wr_one : (qExpansion 1 wr).coeff 1 = -1728 := by
  rw [qExp_wr]
  simp only [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_succ, coeff_Df, smul_eq_mul]
  norm_num [E₄_qExpansion_coeff_one, E₆_qExpansion_coeff_one,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩,
    -PowerSeries.coeff_zero_eq_constantCoeff]

private lemma wr_ne_zero (τ : ℍ) : wr τ ≠ 0 := by
  have hcusp : IsCuspForm wrForm := (isCuspForm_iff_coeffZero_eq_zero _).mpr coeff_wr_zero
  obtain ⟨g, hg⟩ := hcusp
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hgE : (g : ℍ → ℂ) = wr := congrArg DFunLike.coe hg
  have hcΔ : (c • CuspForm.discriminant : ℍ → ℂ) = wr := (congrArg DFunLike.coe hc).trans hgE
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := coeff_wr_one
    rw [← hcΔ, zero_smul, UpperHalfPlane.qExpansion_zero, map_zero] at h
    norm_num at h
  rw [← hcΔ]
  exact mul_ne_zero hc0 (discriminant_ne_zero τ)

theorem wronskian_E₄_E₆_ne_zero : ∀ τ : ℍ,
    2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ - 3 * E₆ τ * deriv (⇑E₄ ∘ ofComplex) τ ≠ 0 := by
  intro τ h
  apply wr_ne_zero τ
  simp only [wr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    Derivative.normalizedDerivOfComplex]
  linear_combination (2 * π * I : ℂ)⁻¹ * h

end GlobalTheory.EisWronskian
