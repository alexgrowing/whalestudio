import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckExistenceClosedSubschemesSeparated
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieck_existence_closedSubschemes_separated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isSeparated | exact GlobalTheory.FormalAlg.alg_of_isSeparated | (intros; apply GlobalTheory.FormalAlg.alg_of_isSeparated <;> assumption)
