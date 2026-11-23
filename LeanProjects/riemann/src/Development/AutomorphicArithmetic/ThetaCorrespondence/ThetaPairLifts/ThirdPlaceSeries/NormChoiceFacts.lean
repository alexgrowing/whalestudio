import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
structure CoreNormFacts (D : D7) : Prop where
  what₂ : _root_.GlobalTheory.NRows.PointConditions' D
  adm : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D
  Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
  Conclusion2 : SumRepresentations.Conclusion2 D
  rhoBar : ResidualIrreducibleRankR D
  g3p : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  g2 : _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D ∧ _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D
  admJ : ∀ L : SizeData₂ D, AdmissibleParameterJ.AdmPar L → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D
structure NormChoiceFacts (D : D7) (C : NChoice D) : Prop extends toCore : _root_.GlobalTheory.NFacts.CoreNormFacts D where
  c2 : KillingConditions.LocalisationUniqueness D
  large : GlobalTheory.CoefDuty.Large D
  duties : GlobalTheory.CoefDuty.Duties D
  nct : NChTie D C
  trip : GlobalTheory.PtCore.TriplesGood D
  same : GlobalTheory.PtCore.SameTwist D C
  good : GoodFTAll D
theorem CoreNormFacts.admA {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D := h.adm.1.1
theorem CoreNormFacts.a3 {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := h.what₂.rank L
theorem CoreNormFacts.isot {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) : Rows.IsotInternal D.what₂ := h.adm.2.2
end GlobalTheory.NFacts
end
end
