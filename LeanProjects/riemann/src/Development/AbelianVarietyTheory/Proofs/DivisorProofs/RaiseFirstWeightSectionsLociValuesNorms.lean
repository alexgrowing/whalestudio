import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem upAtPrime_groups_values_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (u : SmFn p) (a b : ℤ), (upperParabolic P u).H a b = P.H a b ∧ (∀ f, NV (upperParabolic P u) a b f = NV P a b f) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), val (upperParabolic P u) a b σ y f = val P a b σ y f * (Real.exp (-(a * u.u σ y) / 2) : ℝ) ∧ (upperParabolic P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(a * u.u σ y) / 2) := by
  intro k _ X _ p P u a b
  have key : ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      Real.exp (-(a * ((upperParabolic P u).L.φ σ).φ (pick ((upperParabolic P u).L.φ σ).isLB y) y + b * ((upperParabolic P u).A.φ σ).φ (pick ((upperParabolic P u).A.φ σ).isLB y) y) / 2)
        = Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)
          * Real.exp (-(a * u.u σ y) / 2) := by
    intro σ y
    rw [← Real.exp_add]
    congr 1
    show -(a * ((P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + u.u σ y) + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 = _
    ring
  refine ⟨rfl, fun f => rfl, fun σ y f => ⟨?_, ?_⟩⟩
  · show ratVal _ y * ((Real.exp _ : ℝ) : ℂ) = ratVal _ y * ((Real.exp _ : ℝ) : ℂ) * _
    rw [key σ y, Complex.ofReal_mul, mul_assoc]
    rfl
  · show ‖ratVal _ y‖ * Real.exp _ = ‖ratVal _ y‖ * Real.exp _ * _
    rw [key σ y, mul_assoc]
    rfl

end GlobalTheory.HSAmp
