import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTriangularFactorUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_triangular_factor_unique : ∀ (R : Type) [CommRing R] (m : ℕ) (n n' : Low m → R) (M M' : Matrix (Fin m) (Fin m) R), M.BlockTriangular id → M'.BlockTriangular id → IsUnit M.det → uniR n * M = uniR n' * M' → n = n' := by
  first | exact @GlobalTheory.FlagCell.uniR_unique_of_mul_eq | exact GlobalTheory.FlagCell.uniR_unique_of_mul_eq | (intros; apply GlobalTheory.FlagCell.uniR_unique_of_mul_eq <;> assumption)
