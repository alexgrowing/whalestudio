import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.BeBesselOf

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.S5
open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.Cv PI.WBL.Cv.BeC
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace G

theorem beBessel_of (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeBessel := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hSide v hv ξ
  obtain ⟨-, hDI, -, -⟩ := hIn
  obtain ⟨hlam, hds, hgap, hOK, hw0, hz, hT, hc, hπ, hμW, hμN, hμG, hq⟩ := hSide
  have : SigmaFinite μN := hμN.1
  have hds' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ := hds
  have hπ' : Formalism.MainNotions.S.IsHCTypeW k r z u π := hπ
  have hw0' : Formalism.MainNotions.S.IsLowUnitH k r ε lam σ w0 := hw0
  have hM := Formalism.MainNotions.MeasFS.measF_side hz hT hπ hμW hμN
  set a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h with ha_def
  obtain ⟨ha1, hAG, -⟩ := PI.WBL.NIS.thresholds hOK.2.2.1
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hAG' : Formalism.FourierDecayAlt.ThreeDimData.AG k r < a - 1 := by linarith
  have hgr0 := hGS k r z μW μN μG νq (a - 1) hz hT hμW hμN hμG hq hAG'
  have hgr : Integrable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 : Mx k r) ^ (1 - a)) (μW.prod μN) := by
    refine hgr0.congr (ae_of_all _ fun p => ?_)
    simp only [neg_sub]
  have hK : PtDec σ a (fun v => Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v) := by
    intro v0 hv0
    obtain ⟨C, Ws, hWs, hb⟩ := hDI k r ε lam h H σ hlam hds hgap hOK v0 hv0
    refine ⟨C, Ws, hWs, fun w hw x hx => ?_⟩
    have := hb w hw x hx
    simpa only [dsigW_eq] using this
  have hB : Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z (psi k r z c) σ π
      (fun x => (∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ x v p ∂(μW.prod μN)) ξ) := by
    rcases hv with hvD | hvK
    · have h0 : PtB σ a w0 := hK w0 (Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0')
      exact Formalism.MainNotions.BeBesselW.beBessel_DD (u := u) z c π μW μN σ w0 a hds' hz hT hπ' hM hgr ha1 h0 v hvD ξ
    · exact Formalism.MainNotions.BeBesselW.beBessel_K (u := u) z c π μW μN σ a hds' hz hT hπ' hM hgr hK v hvK ξ
  obtain ⟨h1, h2, h3, h4⟩ := hB
  exact ⟨h1, h2, h3, cwCont_conv h4⟩

end G

end PI.WBL.S5

end
