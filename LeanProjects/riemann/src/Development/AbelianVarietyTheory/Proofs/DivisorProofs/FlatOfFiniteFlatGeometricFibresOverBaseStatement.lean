import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteFlatGeometricFibresOverBase
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_finite_flat_geometric_fibres_over_base : ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom →
    LocallyOfFinitePresentation Y.hom → IsFinite f.left →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Flat ((Over.pullback t).map f).left) →
    Flat f.left := by
  first | (exact @GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over) | (exact GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over) | (intros; apply GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over <;> assumption)
