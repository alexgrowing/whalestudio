import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleThreePrime
import Formalism.SharpRestriction.LevelLetterCocycles.AutomorphicSideWildInertia
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps

noncomputable section

namespace GlobalTheory.NFacts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

structure Core (D : D7) : Prop where
  what₂ : GlobalTheory.NRows.Rows D
  adm : SumRepresentations.admitted D
  Conclusion1 : SumRepresentations.Conclusion1 D
  Conclusion2 : SumRepresentations.Conclusion2 D
  rhoBar : ResidualIrreducibleRankR D
  g3p : AdmissibleThreePrime.LabelDegreeHypotheses D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  g2 : AdmissibleParameterJ.DeRhamFamilyAway D ∧ AdmissibleParameterJ.DeRhamFamilyTypePrimes D
  admJ : ∀ L : SizeData₂ D, AdmissibleParameterJ.AdmPar L → AdmissibleParameterJ.AdmJ L
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D

structure Facts (D : D7) (C : NChoice D) : Prop extends Core D where
  c2 : KillingConditions.LocalisationUniqueness D
  large : GlobalTheory.CoefDuty.Large D
  duties : GlobalTheory.CoefDuty.Duties D
  nct : NChTie D C
  trip : GlobalTheory.PtCore.TriplesGood D
  same : GlobalTheory.PtCore.SameTwist D C
  good : GoodFTAll D

theorem Core.admA {D : D7} (h : Core D) : SumRepresentations.AdmA D := h.adm.1.1

theorem Core.a3 {D : D7} (h : Core D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := h.what₂.rank L

theorem Core.isot {D : D7} (h : Core D) : Rows.IsotInternal D.what₂ := h.adm.2.2

theorem residualIrreducibility_forms_equivalent (D : D7) : SumRepresentations.adm6 D ↔ ResidualIrreducibleRankR D := Iff.rfl

end GlobalTheory.NFacts

end
