import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreDimensionLe
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_dimension_le : ∀ (B Y : Scheme.{0}) [IsIntegral B] (d e : ℕ), topologicalKrullDim B = (d : ℕ) → topologicalKrullDim Y ≤ (d + e : ℕ) → ∀ (f : Y ⟶ B) [UniversallyClosed f] (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → topologicalKrullDim G ≤ (e : ℕ) := by
  first | exact @GlobalTheory.GenFibreDim.topologicalKrullDim_genericFibre_le | exact GlobalTheory.GenFibreDim.topologicalKrullDim_genericFibre_le | (intros; apply GlobalTheory.GenFibreDim.topologicalKrullDim_genericFibre_le <;> assumption)
