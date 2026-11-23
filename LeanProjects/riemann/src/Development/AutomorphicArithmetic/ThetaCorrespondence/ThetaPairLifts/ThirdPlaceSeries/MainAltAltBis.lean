import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RxCrys

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
theorem main_alt_alt : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i → GoodR D.nd i r → (Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x)))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  intro D i r ρ π h41 hfont hr hρc hd hl0 hl1 w hw C
  have hF := hfont w hw C
  have hcA : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r := continuous_family_of D i r hr
  have hrx := _root_.GlobalTheory.CrysChiOne.rx_crys_alt_alt h41 r hr hl0 hl1 C
  have hchi := chi1inv_crys C hF r ρ π hd (hrx π) (hcA π)
  have hTw : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    intro x
    have hc' := locC_cont' C _ (rTwO_cont D i r hcA x)
    rw [locC_rTwO] at hc' ⊢
    exact twist_crys C hF _ _ (locC_cont' C _ (hcA x)) hc' hchi (hrx x)
  obtain ⟨B, A, hAB, hint⟩ := decomp_rho r ρ π hd
  have hrho := sub_crys C hF r π (hrx π) (hcA π) (rhoO D.nd i ρ π) hρc B A hAB hint
  have hWc : Continuous fun g => WpO D.nd i ρ π g := by
    have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
      have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
          fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
        funext g
        rw [map_inv]
        rfl
      rw [e]
      exact (D.nd.chi_cont i 1).comp continuous_inv
    exact h1.smul hρc
  have hW : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) := by
    have hc' := locC_cont' C _ hWc
    rw [locC_WpO] at hc' ⊢
    exact twist_crys C hF _ _ (locC_cont' C _ hρc) hc' hchi hrho
  refine ⟨hchi, fun x => ?_, hW, ?_⟩
  · rw [locC_rDuO]
    exact (GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL _ hF.2.2.1
      (locC_cont' C _ (rTwO_cont D i r hcA x)) (hTw x)).2
  · rw [locC_T2O]
    exact (GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL _ hF.2.2.1
      (locC_cont' C _ hWc) hW).2
end GlobalTheory.CrysChiOne
end
end
