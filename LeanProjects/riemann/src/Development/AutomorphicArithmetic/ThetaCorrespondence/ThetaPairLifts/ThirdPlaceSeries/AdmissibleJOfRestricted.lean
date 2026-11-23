import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleJOfRestricted
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamPointsWeightJumps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LgcOfCut
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigPdHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisClauseOfSufficient
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory GlobalTheory.StringRepresentationDecomposition UpperTheory.GalC
theorem g3a_of_restricted_general_alt {D : D7} (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : DeRhamJumpsDistinctCondition D) : ∀ i r, GoodR D.nd i r → DistinctAbsIrredConstituents D.nd i r := h.2
theorem admJ_of_admPar (D : D7) (L : SizeData₂ D) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D)
    (hC : CutRec D) (hW : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D) (hB : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D) (hP : AdmissibleParameterJ.AdmPar L) :
    _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L :=
  have hG := _root_.UpperTheory.GalS.de_rham_points_weight_jumps_alt D h0 h1 h2 h5 hC
  ⟨hG.1, GlobalTheory.CrysWD.crysIffWD D, hG.2, _root_.GlobalTheory.T.admDict_of_weight_blockChar GlobalTheory.Published.cheb_holds D h2 hW hB, GlobalTheory.T.hodgeTateJumpsReading_rowAdm D, hP⟩
theorem duties_of_large_aux41 (hC : GlobalTheory.TwSys.Cheb) (D : D7) (hL : GlobalTheory.CoefDuty.Large D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hg : _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D)
    (hRho : AutomorphicSideWildInertia.ResidualIrreducibleGood D) : GlobalTheory.CoefDuty.Duties D :=
  ⟨hL.1, fun i r hr => jc_of_u hr hL.2.1 (_root_.UpperTheory.GalS.g3a_of_restricted_general_alt h41 hg i r hr), GlobalTheory.T.designConditionAll_of_cheb_of_takenAll hC D hL.2.2, GlobalTheory.T.rowFiveOneTypePrime_of_coefRingTakenAtLive hC D hRho hL.2.2⟩
theorem prvG5_of_admissible_cutRec : LocalFiniteness → LocalTateDuality → LocalEulerChar →
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → CutRec D → SumRepresentations.ConclusionG5 D := by
  intro h1 h2 h3 D hA hRb hC
  have hLGC : _root_.GlobalTheory.StringRepresentationDecomposition.LocalGlobalCompatible D := _root_.UpperTheory.GalS.lgc_of_cut'_alt D hA.1.1 hC
  have hEig : EigPd D := _root_.UpperTheory.GalS.eigPd_holds_alt D hA.1.1 hLGC hRb
  have hH : HOneTwo D := GlobalTheory.T.hOneTwo_of_localFiniteness_tateDuality_eulerChar h1 h2 h3 D
  refine _root_.Formalism.MainNotions.SumRepresentations.galois_clause_of_sufficient_alt D hA.1.1 fun i hg r hr w hw => ⟨hLGC i r hr w hw, fun hS => ⟨hRb i hg, fun rb hrb => ?_⟩⟩
  have hS' := (D.nd.S_def i w).1 hS
  have hnr : ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) := by
    have hk : ∀ k, w ∈ placesOver D.host.E (D.host.g k) → D.nd.l i ≠ D.host.g k :=
      fun k hk h => hS'.2 (h ▸ hk)
    rcases hS'.1 with h0 | h0 | h0
    · exact (hA.2.1 i hg rb hrb).2 0 (hk 0 h0) w h0
    · exact (hA.2.1 i hg rb hrb).2 1 (hk 1 h0) w h0
    · exact hEig i hg w hS h0 rb hrb
  exact ⟨hnr, hH i rb w hS hrb hnr⟩
end UpperTheory.GalS
end
end
