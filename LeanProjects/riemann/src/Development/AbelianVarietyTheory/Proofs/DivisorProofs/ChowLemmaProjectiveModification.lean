import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverIsIsoMorphismRestrict
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineLeOrDisjoint
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FormalAlg

theorem exists_isProper_isImmersion_isProjOver : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Nonempty W → ∃ (W' P : Scheme.{0}) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R)) (U : W.Opens), IsProper π ∧ (U : Set W).Nonempty ∧ IsIso (π ∣_ U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s ∧ IsImmersion q ∧ q ≫ s = π ≫ f := by
  first
  | exact @_root_.GlobalTheory.DenseClosedAffineSubsets.chow
  | exact _root_.GlobalTheory.DenseClosedAffineSubsets.chow
  | (apply _root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenseClosedAffineSubsets.chow ..)

end GlobalTheory.FormalAlg
