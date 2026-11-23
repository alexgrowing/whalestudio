import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkReducedClosedGenericPointEqRank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_stalk_reducedClosed_genericPoint_eq_rank : ∀ (X : Scheme.{0}) (Z : Closeds X) [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme] (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [GlobalTheory.QCoh.IsFiniteQC G], Module.length (X.presheaf.stalk (redι Z (genericPoint _))) (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) = (GlobalTheory.VB.genRank G : ℕ∞) := by
  first | exact @GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint | exact GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint | (intros; apply GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint <;> assumption)
