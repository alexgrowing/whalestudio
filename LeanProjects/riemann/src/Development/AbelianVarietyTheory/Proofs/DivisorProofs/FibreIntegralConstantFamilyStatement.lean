import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIntegralConstantFamily
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integral_constant_family : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M 1) (α β : (famAtlas A).Fld), (famAtlas A).IsRealForm 1 α → (famAtlas A).IsRealForm 1 β → (∀ x, (famAtlas A).ddc α x + (famAtlas A).ddc β x = 0) → ∀ t t' : OnePoint ℂ, A.integral ((famAtlas A).pullback A (fib t) α) + A.integral ((famAtlas A).pullback A (fib t) β) = A.integral ((famAtlas A).pullback A (fib t') α) + A.integral ((famAtlas A).pullback A (fib t') β) := by
  first | exact @GlobalTheory.BcUnique.integral_fib_add_const | exact GlobalTheory.BcUnique.integral_fib_add_const | (intros; apply GlobalTheory.BcUnique.integral_fib_add_const <;> assumption)
