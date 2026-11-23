import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topologicalKrullDim_closure_point_le : ∀ (X : Scheme.{0}) (n : ℕ) (z : X), topologicalKrullDim X = n → ∃ e : ℕ, e ≤ n ∧ topologicalKrullDim (closure ({z} : Set X)) = e ∧ ∀ x, z ⤳ x → x ≠ z → 1 ≤ e := by
  first | exact @GlobalTheory.closure_point_topologicalKrullDim | exact GlobalTheory.closure_point_topologicalKrullDim | (intros; apply GlobalTheory.closure_point_topologicalKrullDim <;> assumption)
