import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingResidueFieldFiniteOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelLocalRing_residueField_finite_of_closedPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Finite (ResidueField (M.O x)) := by
  first | exact @GlobalTheory.ResFin.finite_residueField_O | exact GlobalTheory.ResFin.finite_residueField_O | (intros; apply GlobalTheory.ResFin.finite_residueField_O <;> assumption)
