import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SesqEqZeroOfDiagEqZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsOpIntIntegrable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCoeffIdempotentOfOrthogonality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegratedOperatorIsStarProjectionAndSandwich
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteAndIsInvInvariantOfContinuousIntegrab
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricIntertwinerOfMatrixCoeffEq

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.Dec

theorem projAbs_holds : ProjAbs := by
  intro G _ _ _ _ _ _ μ _ _ H _ _ _ σ hσ hσc d hd hS w hw hint
  have hcont : ∀ x y : H, Continuous fun g => ⟪y, σ g x⟫_ℂ := fun x y =>
    continuous_const.inner (hσc x)
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hm1 : ⟪w, σ 1 w⟫_ℂ = 1 := by
    rw [map_one, ContinuousLinearMap.one_apply, hww]
  obtain ⟨hsf, hinv⟩ := GlobalTheory.sigmaFinite_and_isInvInvariant_of_continuous_integrable G μ (fun g => ⟪w, σ g w⟫_ℂ) (hcont w w)
    (by show ⟪w, σ 1 w⟫_ℂ ≠ 0; rw [hm1]; exact one_ne_zero) hint
  have hpol := GlobalTheory.polarised_schur_relations G μ H σ d (fun x y => (hcont x y).aestronglyMeasurable) hS
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.matrixCoeff_idempotent_of_orthogonality G μ H σ d hd hσ (fun v w v' w' => (hpol v w v' w').2) w hw
  have hφ : Integrable (phG d σ w) μ := by
    have : Integrable (fun g => star ⟪w, σ g w⟫_ℂ) μ :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hint
    exact this.const_mul (d : ℂ)
  refine ⟨h1, h2, ?_⟩
  intro Hp _ _ _ π hπ hπc
  refine ⟨?_, ?_⟩
  · obtain ⟨P, -, hP⟩ := GlobalTheory.absOpInt G μ Hp π hπ hπc (phG d σ w) hφ
    exact ⟨P, hφ, hP⟩
  intro P hP
  obtain ⟨hsp, hPxP⟩ := GlobalTheory.integratedOperator_isStarProjection_and_sandwich G μ Hp π hπ hπc (phG d σ w) (fun x => ⟪w, σ x w⟫_ℂ) hφ h1 h2 hm1
    P hP.2
  have hfix : ∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), P v = v := by
    rintro _ ⟨u, rfl⟩
    have := congrArg (fun T : Hp →L[ℂ] Hp => T u) hsp.isIdempotentElem.eq
    simpa using this
  have hunit : ∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), ‖v‖ = 1 →
      (∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) ∧
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
    intro v hv hn
    have hPv := hfix v hv
    have hc : ∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ := by
      intro g
      have hvv : ⟪v, v⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hn]; simp
      have e1 : P (π g v) = ⟪w, σ g w⟫_ℂ • v := by
        have := congrArg (fun T : Hp →L[ℂ] Hp => T v) (hPxP g)
        simpa [hPv] using this
      have hadj : ContinuousLinearMap.adjoint P = P := by
        rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsp.isSelfAdjoint
      calc ⟪v, π g v⟫_ℂ = ⟪ContinuousLinearMap.adjoint P v, π g v⟫_ℂ := by rw [hadj, hPv]
        _ = ⟪v, P (π g v)⟫_ℂ := ContinuousLinearMap.adjoint_inner_left _ _ _
        _ = ⟪w, σ g w⟫_ℂ := by rw [e1, inner_smul_right, hvv, mul_one]
    exact ⟨hc, GlobalTheory.exists_isometric_intertwiner_of_matrixCoeff_eq G H σ Hp π hσ hπ w v h4 hc⟩
  refine ⟨hsp, hPxP, hunit, ?_⟩
  ext v
  constructor
  · intro hv
    by_cases h0 : v = 0
    · exact ⟨0, fun g => by simp, by simp [h0]⟩
    · have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hv' : ((‖v‖ : ℂ)⁻¹ • v) ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp) := Submodule.smul_mem _ _ hv
      obtain ⟨-, io, hio, hint'⟩ := hunit _ hv' (norm_smul_inv_norm h0)
      refine ⟨(‖v‖ : ℂ) • io.toContinuousLinearMap, fun g => ?_, ?_⟩
      · ext u
        simp [hint']
      · show v = (‖v‖ : ℂ) • io w
        rw [hio, smul_smul, mul_inv_cancel₀ hn, one_smul]
  · rintro ⟨io, hio, rfl⟩
    refine ⟨io w, ?_⟩
    show P (io w) = io w
    refine ext_inner_left ℂ fun x => ?_
    have e : ∀ g, ⟪x, π g (io w)⟫_ℂ = ⟪ContinuousLinearMap.adjoint io x, σ g w⟫_ℂ := by
      intro g
      rw [ContinuousLinearMap.adjoint_inner_left]
      have := congrArg (fun T : H →L[ℂ] Hp => T w) (hio g)
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this]
    rw [hP.2]
    simp only [e]
    have := h3 w (ContinuousLinearMap.adjoint io x)
    rw [hww, one_mul, ContinuousLinearMap.adjoint_inner_left] at this
    exact this

end GlobalTheory.Dec
