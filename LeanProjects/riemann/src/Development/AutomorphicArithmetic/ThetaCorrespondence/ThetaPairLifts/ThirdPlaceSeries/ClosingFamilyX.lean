import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointConditionsRangeBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleJOfRestricted
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointInputAwayFromTypePrimesStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory
theorem closingFamilyX_alt_alt : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D) (X : KillingConditions.HubData D), _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.PtCore.PtFam D X.r X.ρ → (∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i) → (∀ i, AbsIrreducibleDistinct D i (X.r i)) ∧ (∀ i, KillingConditions.RangeAD large₂ X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i)) ∧ (∀ i π, EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i))
:= by
  intro hF hK D HW F large₂ X hJ hA hP h41 hO hX hcB
  refine ⟨fun i => UpperTheory.GalS.jc_of_u (hX.good i) hO (_root_.UpperTheory.GalS.g3a_of_restricted_general_alt h41 hA.2.2.1 i _ (hX.good i)), fun i hR π => ?_,
    fun i hl π hπ => ?_, fun i π => GlobalTheory.Pass.ambient_h1f_of_local_finiteness hK D i _ π _ (hX.cont i π)⟩
  · exact GlobalTheory.BlockWindow.jointCond_TB_at_range D HW F large₂ (hJ large₂ hA) hP i _ π _ (fun h => hR.1 (Or.inl h))
      (fun h => hR.2.1 (Or.inl h)) (fun h => hR.2.1 (Or.inr h)) (hX.good i) (hcB i)
  · have hp := _root_.GlobalTheory.T.ptIn_of_ptFam_deRham_away hF D X hX hA.1 i hl π hπ
    intro _ w hw _ C τ a
    have hd : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (X.r i π) (X.ρ i π) (D.nd.chi i) e := by
      obtain ⟨e, he⟩ := hp.dec
      exact ⟨e, fun g u => he g u⟩
    have := D.nd.lPrime i
    have := C.LL.2
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ C.LL _ _ (hp.crys w hw C π)).1
    exact (((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le (X.r i) (X.ρ i) π hd).2 hdr).2.2 τ a).2
end GlobalTheory
end
