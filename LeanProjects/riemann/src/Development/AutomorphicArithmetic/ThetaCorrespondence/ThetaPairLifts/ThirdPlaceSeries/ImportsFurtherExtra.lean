import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetPointGood

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.NLink.AmbSub
variable {D : D7}
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambSub i (X.r i) π (X.dc i) ∧ EmbeddingTypes.ambCont i (X.r i) (X.ρ i) π ∧ EmbeddingTypes.ColumnH0Vanishing i (X.ρ i) π (X.dc i) := by
  intro hP D L P nch HW F Cm X C₂ hSet i hi π hπ
  have hS := _root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hSet i hi π hπ
  obtain ⟨_, hG2, _, _, _, _, _, _, hCont, _, _, _, _, _, hFont, _, _⟩ := hS
  have hρ : Continuous fun g => ((X.ρ i π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := hSet.canon.fam.cont i π
  have hcx : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) (v : Fin D.R.nV → ↥C.LL.1),
      Continuous fun g => (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x) g).mulVec v :=
    fun w hw C x v => locC_cont D i _ (rTwO_cont D i (X.r i) hCont x) w hw C v
  have hcr : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) := by
    intro w hw C x
    rw [locC_rTwO]
    exact (hG2 w hw C).2 x
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ w hw _ C A hA
    have hJ : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) π))) τ a} := by
      intro x τ
      refine jumps_of_multV_eq (O := ↥(OL C.LL)) (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C)
        (hFont w hw C) x π (hcr w hw C x) (hcr w hw C π) τ (fun a => ?_)
      rw [locC_rTwO, locC_rTwO]
      exact (hG2 w hw C).1.2.1 τ x π a
    exact subsum_crys (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C) (hFont w hw C)
      (hcr w hw C) hJ A hA
  · intro w hw C
    refine ⟨fun x v => hcx w hw C x v, fun _ => ⟨fun v => ?_, fun v => ?_⟩⟩
    · exact locC_cont D i _ (WpO_cont i (X.ρ i) π hρ) w hw C v
    · exact locC_cont D i _ (GlobalTheory.TwistedDualLoc.continuous_T2O D i (X.ρ i) π hρ) w hw C v
  · intro _ w hw _ C
    exact (hG2 w hw C).1.2.2.2.2.2.1
end GlobalTheory.NLink.AmbSub
end
end
