import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticZeroDimensionalFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
open CategoryTheory AlgebraicGeometry GlobalTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_zero_dimensional_finite : ∀ (k : Type) [CommRing k] (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'],
    IsArithVar (spMap (algebraMap k k')) 0 → Module.Finite ℤ k' := by
  first | exact @GlobalTheory.IsArithVar.moduleFinite_int_of_spec | exact GlobalTheory.IsArithVar.moduleFinite_int_of_spec | (intros; apply GlobalTheory.IsArithVar.moduleFinite_int_of_spec <;> assumption)
