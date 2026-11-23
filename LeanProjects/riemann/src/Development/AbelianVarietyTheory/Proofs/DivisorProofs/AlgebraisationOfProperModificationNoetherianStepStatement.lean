import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationOfProperModificationNoetherianStep
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraisation_of_proper_modification_noetherian_step : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → ∀ (W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) → ∀ K : W.IdealSheafData, (∀ x, x ∉ K.support → x ∈ U) → Alg (π ≫ f) I → (∀ k : ℕ, Alg ((K ^ k).subschemeι ≫ f) I) → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_modification | exact GlobalTheory.FormalAlg.alg_of_modification | (intros; apply GlobalTheory.FormalAlg.alg_of_modification <;> assumption)
