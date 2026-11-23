import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEq
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp F) (n : ℕ), Smooth q → topologicalKrullDim X = n → SmoothOfRelativeDimension n q := by
  first | exact @GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | exact GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | (intros; apply GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq <;> assumption)
