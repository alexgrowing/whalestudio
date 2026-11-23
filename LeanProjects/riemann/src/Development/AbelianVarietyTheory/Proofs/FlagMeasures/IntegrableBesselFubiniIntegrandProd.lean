import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormCoeffProductFubiniIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.SgInf

theorem prod_integrand_integrable : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v (Matrix.of p.2 * Matrix.of p.1)) * ⟪PiS (psiGen k r z c) π (Matrix.of p.2)⁻¹ ξ, ξ⟫_ℂ) (μG.prod μS) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have hF := GlobalTheory.T.besselForm_coeff_product_fubini_integrable k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv v hv
  obtain ⟨hz, hT, hπ, hHaarS, _⟩ := hSide
  have : SigmaFinite μS := hHaarS.1
  have : SigmaFinite μG := hStd.2.2.2.2.1.1
  obtain ⟨-, -, hPiB, hPiC, -⟩ := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  have hS : IsClosedSub k r (Sset k r z) := (closedSub_groups k r z hz hT).2.2.2.1

  set T : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ Sset k r z} with hTdef
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hTm : MeasurableSet T := (hS.2.1.preimage hof).measurableSet
  have haeT : ∀ᵐ x ∂μS, x ∈ T := ae_iff.2 hHaarS.2.2.1

  have hinv : ContinuousOn (fun x : Mt k r => (Matrix.of x : Mat k r)⁻¹) T := by
    intro x hx
    have hg : (Matrix.of x : Mat k r)ᴴ * Hpk k r * (Matrix.of x : Mat k r) = Hpk k r := hS.1 hx
    have hH := Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r
    have hdet : IsUnit (Matrix.of x : Mat k r).det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      have h1 := congrArg Matrix.det hg
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
      exact hH.ne_zero h1.symm
    have hc : ContinuousAt Ring.inverse (Matrix.of x : Mat k r).det := by
      simpa using NormedRing.inverse_continuousAt hdet.unit
    exact ((continuousAt_matrix_inv _ hc).comp hof.continuousAt).continuousWithinAt
  have hmaps : Set.MapsTo (fun x : Mt k r => (Matrix.of x : Mat k r)⁻¹) T (Sset k r z) :=
    fun x hx => hS.2.2.2.2 _ hx
  have hgc : ContinuousOn
      (fun x : Mt k r => ⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ) T :=
    ((hPiC.comp hinv hmaps).clm_apply continuousOn_const).inner continuousOn_const
  have hgm : AEStronglyMeasurable
      (fun x : Mt k r => ⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ) μS := by
    have h1 := hgc.aestronglyMeasurable (μ := μS) hTm
    rwa [Measure.restrict_eq_self_of_ae_mem haeT] at h1

  have hbd : ∀ x ∈ T,
      ‖⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ‖ ≤ ‖ξ‖ * ‖ξ‖ := by
    intro x hx
    have h1 := (hPiB _ (hmaps hx)).1
    calc _ ≤ ‖PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ‖ * ‖ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ξ‖ * ‖ξ‖ := by
        gcongr
        calc _ ≤ ‖PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹‖ * ‖ξ‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖ξ‖ := by gcongr
          _ = ‖ξ‖ := one_mul _
  have haeP : ∀ᵐ p ∂(μG.prod μS), p.2 ∈ T := by
    rw [ae_iff]
    have h1 : {p : Mt k r × Mt k r | ¬ p.2 ∈ T} = Set.univ ×ˢ {x | ¬ x ∈ T} := by
      ext p; simp
    rw [h1, Measure.prod_prod, ae_iff.1 haeT, mul_zero]
  refine hF.mul_bdd (c := ‖ξ‖ * ‖ξ‖)
    (hgm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd) ?_
  filter_upwards [haeP] with p hp
  exact hbd p.2 hp

end GlobalTheory.SgInf
