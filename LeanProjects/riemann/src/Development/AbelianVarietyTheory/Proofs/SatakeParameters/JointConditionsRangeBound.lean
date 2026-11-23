import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleDistinctConstituents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AmbientH1fOfLocalFiniteness
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointInFamilyCrystallineStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem closingFamilyX : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D) (X : KillingConditions.HubData D), AdmissibleParameterJ.JumpBoundClosedForm D → AdmissibleParameterJ.AdmJ large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.PtCore.PtFam D X.r X.ρ → (∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i) → (∀ i, AbsIrreducibleDistinct D i (X.r i)) ∧ (∀ i, KillingConditions.RangeAD large₂ X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i)) ∧ (∀ i π, EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i))
:= by
  intro hF hK D HW F large₂ X hJ hA hP h41 hO hX hcB
  refine ⟨fun i => GlobalTheory.abs_irreducible_distinct_constituents D h41 hO i _ (hX.good i), fun i hR π => ?_,
    fun i hl π hπ => ?_, fun i π => GlobalTheory.Pass.ambient_h1f_of_local_finiteness hK D i _ π _ (hX.cont i π)⟩
  · exact GlobalTheory.BlockWindow.jointCond_TB_at_range D HW F large₂ (hJ large₂ hA) hP i _ π _ (fun h => hR.1 (Or.inl h))
      (fun h => hR.2.1 (Or.inl h)) (fun h => hR.2.1 (Or.inr h)) (hX.good i) (hcB i)
  · have hp := GlobalTheory.T.point_in_family_crystalline hF D X hX hA.1 i hl π hπ
    intro _ w hw _ C τ a
    have hd : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (X.r i π) (X.ρ i π) (D.nd.chi i) e := by
      obtain ⟨e, he⟩ := hp.dec
      exact ⟨e, fun g u => he g u⟩
    have := D.nd.lPrime i
    have := C.LL.2
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ C.LL _ _ (hp.crys w hw C π)).1
    exact (((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le (X.r i) (X.ρ i) π hd).2 hdr).2.2 τ a).2

end GlobalTheory
