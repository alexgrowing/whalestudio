import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.QuotInt

theorem opn_continuous {n : ℕ} : Continuous (opn : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  have h : Continuous fun g : Matrix (Fin n) (Fin n) ℂ =>
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := fun g => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g
         map_add' := fun a b => map_add _ a b
         map_smul' := fun c a => map_smul _ c a } :
        Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
  exact h.norm

end GlobalTheory.SgInf.QuotInt

namespace GlobalTheory.SgInf

open GlobalTheory.SgInf.QuotInt in

theorem integrable_Afun_quotMeas : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu v hv ξ
  have hStd' := hStd
  have hSide' := hSide
  obtain ⟨hk, hrep, -, -, hHaar, -, ha, hdec, -⟩ := hStd'
  obtain ⟨hz, hT, hπ, hHaarS, -⟩ := hSide'
  have hcl := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  have hG : IsClosedSub k r (GG k r) := hcl.1
  have hS : IsClosedSub k r (Sset k r z) := hcl.2.2.2.1
  have hunim : IsUnimod (Sset k r z) μS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hHaarS
  have hW := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hS hHaar hHaarS hunim hν
  have hνG : ν {x | Matrix.of x ∉ GG k r} = 0 := hW.2.1
  have hstab := (GlobalTheory.SgInfDD.DD_stable_dense k r σ w hrep).1
  have hD1 := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hstab hdec u hu v hv
  have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  have hmeasG : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} :=
    (hG.2.1.preimage (f := fun x : Mt k r => (Matrix.of x : Mat k r)) continuous_id).measurableSet
  have haeG : ∀ᵐ x ∂ν, x ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := by
    rw [ae_iff]; simpa using hνG

  have hcont : ContinuousOn (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x))
      {x | Matrix.of x ∈ GG k r} := by
    have h1 : ContinuousOn (fun x : Mt k r => be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v)
        {x | Matrix.of x ∈ GG k r} :=
      hD1.2.2.2.comp (f := fun x : Mt k r => (Matrix.of x : Mat k r)) continuous_id.continuousOn
        (fun x hx => hx)
    exact h1.clm_apply continuousOn_const
  have hae : AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν := by
    have h1 := hcont.aestronglyMeasurable (μ := ν) hmeasG
    rwa [Measure.restrict_eq_self_of_ae_mem haeG] at h1
  refine ⟨hae, ?_⟩

  obtain ⟨C, hC⟩ := hdec u hu v hv
  have hC'0 : 0 ≤ max C 0 := le_max_right _ _
  let f : Mt k r → ENNReal := fun y => ENNReal.ofReal (max C 0 * opn (Matrix.of y : Mat k r) ^ (-a))
  have hopn : Measurable fun y : Mt k r => opn (Matrix.of y : Mat k r) :=
    Continuous.measurable (α := Mt k r) (opn_continuous (n := 2 * r + k + 1))
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hopn.pow_const (-a)))
  have hcoef : ∀ g ∈ GG k r, ‖coef σ u v g‖ₑ ≤ ENNReal.ofReal (max C 0 * opn g ^ (-a)) := by
    intro g hg
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((hC g hg).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (opn_nonneg _) _)
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hHaarS.2.2.1
  have hpt : ∀ x : Mt k r, Matrix.of x ∈ GG k r →
      ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ₑ ≤
        ‖ξ‖ₑ * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x hx
    have h1 : ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ₑ ≤
        ‖be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v‖ₑ * ‖ξ‖ₑ :=
      ContinuousLinearMap.le_opENorm_of_le _ le_rfl
    refine h1.trans ?_
    rw [mul_comm]
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono_ae ?_
    filter_upwards [haeS] with s hs
    have hsG : Matrix.of s ∈ GG k r := hS.1 hs
    have hsi : (Matrix.of s : Mat k r)⁻¹ ∈ Sset k r z := hS.2.2.2.2 _ hs
    have hP : ‖PiS (psiGen k r z c) π (Matrix.of s)⁻¹‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (hPi.2.2.1 _ hsi).1
    have hc : coef σ (σ (Matrix.of x) u) v (Matrix.of s) = coef σ u v (Matrix.of s * Matrix.of x) := by
      simp only [coef, hrep.1.2 _ hsG _ hx, ContinuousLinearMap.comp_apply]
    rw [enorm_smul]
    calc _ ≤ ‖coef σ (σ (Matrix.of x) u) v (Matrix.of s)‖ₑ * 1 := by gcongr
      _ = ‖coef σ u v (Matrix.of s * Matrix.of x)‖ₑ := by rw [mul_one, hc]
      _ ≤ ENNReal.ofReal (max C 0 * opn (Matrix.of s * Matrix.of x : Mat k r) ^ (-a)) :=
        hcoef _ (hG.2.2.2.1 _ hsG _ hx)
  have hfin : ∫⁻ x, f x ∂μG < ⊤ := by
    have hn : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a := by
      have h2 : (1 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 < 2 * r + k + 1)
      have := pow_lt_pow_right₀ h2 (by norm_num : 2 < 5)
      linarith
    have hN := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (GG k r) μG a hG hHaar hn
    have heq : ∫⁻ x, f x ∂μG = ENNReal.ofReal (max C 0) * normInt μG a := by
      rw [normInt, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      exact ENNReal.ofReal_mul hC'0
    rw [heq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN
  unfold HasFiniteIntegral
  calc _ ≤ ∫⁻ x, ‖ξ‖ₑ * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂ν :=
        lintegral_mono_ae (haeG.mono fun x hx => hpt x hx)
    _ = ‖ξ‖ₑ * ∫⁻ x, f x ∂μG := by rw [lintegral_const_mul' _ _ enorm_ne_top, hν f hfm]
    _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top hfin

end GlobalTheory.SgInf
