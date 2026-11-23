import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNorms
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (u : SmFn p) (a b : ℤ), (upperParabolic P u).H a b = P.H a b ∧ (∀ f, NV (upperParabolic P u) a b f = NV P a b f) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), val (upperParabolic P u) a b σ y f = val P a b σ y f * (Real.exp (-(a * u.u σ y) / 2) : ℝ) ∧ (upperParabolic P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(a * u.u σ y) / 2) := by
  first | exact @GlobalTheory.HSAmp.upAtPrime_groups_values_norms | exact GlobalTheory.HSAmp.upAtPrime_groups_values_norms | (intros; apply GlobalTheory.HSAmp.upAtPrime_groups_values_norms <;> assumption)
