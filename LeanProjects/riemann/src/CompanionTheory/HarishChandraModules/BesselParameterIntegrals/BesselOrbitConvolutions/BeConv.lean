import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselIntegralConvergenceOfGrowth

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P
open Formalism.QuantumDeterminants

namespace G

theorem bessel_integral_convergence_of_growth (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  obtain ⟨hHC, hσ, hgap, hOK, hw0, hz, hT, hc, hπ, hW, hN, hG, hQ⟩ := hS
  have hσ' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ := hσ
  have hw0' : Formalism.MainNotions.S.IsLowUnitH k r ε lam σ w0 := hw0
  have : SigmaFinite μN := hN.1
  set a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h with ha_def
  have ha1 : 1 + Formalism.FourierDecayAlt.ThreeDimData.AG k r < a := one_add_AG_lt_aOf hOK
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have ha : 1 ≤ a := by linarith
  have hM := Formalism.MainNotions.MeasFS.measF_side hz hT hπ hW hN
  have hgr0 := hGS k r z μW μN μG νq (a - 1) hz hT hW hN hG hQ (by linarith)
  have hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a))
      (μW.prod μN) := by
    simpa only [neg_sub] using hgr0
  have hDI : PI.WBL.Cv.BeC.DecInf σ a := by
    intro v0 hv0
    obtain ⟨C, Ws, hWs, hb⟩ := hIn.2.1 k r ε lam h H σ hHC hσ hgap hOK v0 hv0
    refine ⟨C, Ws, hWs, fun w hw x hx => ?_⟩
    have e := hb w hw x hx
    simp only [dsigW_eq_bessel_integrability] at e
    exact e
  have hB := PI.WBL.Cv.BeC.beConv_of_low z c π μW μN σ a (PI.WBL.Cv.grpAll k r z)
    (PI.WBL.Cv.sigAll k r ε lam H σ hσ') (PI.WBL.Cv.piAll k r z u Wp π hz hT hπ) (PI.WBL.Cv.psiAll k r z c hz) hM
    (fun w => Formalism.MainNotions.LeviCoordinates.discrete_series_continuousOn hσ' w) ha hgr hDI hw0'

  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    hIn.2.2.1 k r ε lam H σ hHC hσ w0 (Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0')
  have hDDs : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    have hle : Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0 ≤ Formalism.MainNotions.DoubleDerivativeSmoothness.smoothSub σ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, hg, rfl⟩
      exact Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate_unitary (fun _ ha _ hb => Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ' ha hb) hw0s hg
    intro v hv; exact hle hv
  have hAs : ∀ v, Formalism.FourierDecayAlt.ThreeDimData.IsAdm σ w0 v → v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    rintro v (hv | hv)
    · exact hDDs v hv
    · exact hIn.2.2.1 k r ε lam H σ hHC hσ v hv
  obtain ⟨h1, -, h3, -, h5, h6⟩ := hB
  refine ⟨fun x hx v hv => h1 x hx v hv, fun v hv g hg m hm x hx => ?_, fun x hx v hv => h6 x hx v hv,
    fun x hx v hv => ⟨h1 v (hAs v hv) x (Or.inl hx), h5 x (Or.inl hx) v (hAs v hv)⟩⟩
  have e := h3 g hg m hm x hx v hv
  rw [ContinuousLinearMap.smul_comp] at e
  exact e

end G

end Formalism.FourierDecayAlt.P

end
