import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivativeIsDifferential
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exterior_derivative_is_differential : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  first | exact @_root_.GlobalTheory.LogDR.isExtD_extD | exact _root_.GlobalTheory.LogDR.isExtD_extD | (intros; apply _root_.GlobalTheory.LogDR.isExtD_extD <;> assumption)
