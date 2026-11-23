import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_fieldBaseChange_le : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (f' : X' ⟶ Sp K) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k K)) → topologicalKrullDim X' ≤ topologicalKrullDim X := by
  first | exact @GlobalTheory.FieldExtDim.topologicalKrullDim_baseChange_le | exact GlobalTheory.FieldExtDim.topologicalKrullDim_baseChange_le | (intros; apply GlobalTheory.FieldExtDim.topologicalKrullDim_baseChange_le <;> assumption)
