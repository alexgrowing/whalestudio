import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.lbIso_generic_spreads_out_alt : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M N : LB B), QuasiCompact pB → QuasiSeparated pB → M.IsLB → N.IsLB → LBIso (M.pull (pullback.fst pB (spMap (algebraMap R K)))) (N.pull (pullback.fst pB (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → LBIso (M.pull (pullback.fst pB (spMap φ))) (N.pull (pullback.fst pB (spMap φ))) := by
  first | exact @GlobalTheory.lbIso_generic_spreads_out | exact GlobalTheory.lbIso_generic_spreads_out | (intros; apply GlobalTheory.lbIso_generic_spreads_out <;> assumption)
