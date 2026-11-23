import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureLeOfSpecializes
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem topologicalKrullDim_closure_le_of_specializes :
    ∀ (X : Scheme.{0}) (z w : X) (j : ℕ), z ⤳ w → w ≠ z →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      topologicalKrullDim (closure ({w} : Set X)) ≤ j := by
  first
  | exact @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | (apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes ..)

end GlobalTheory.PairStep
