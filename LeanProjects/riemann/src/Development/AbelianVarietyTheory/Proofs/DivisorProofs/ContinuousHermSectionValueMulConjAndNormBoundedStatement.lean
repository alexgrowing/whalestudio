import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBounded
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ), (∀ (σ : k →+* ℂ), ∀ f ∈ P.H a b, ∀ g ∈ P.H a b, Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g)) ∧ ∀ f ∈ P.H a b, (∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f) ∧ ∃ C : ℝ, ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ C := by
  first | exact @GlobalTheory.HSAmp.continuous_val_and_bounded | exact GlobalTheory.HSAmp.continuous_val_and_bounded | (intros; apply GlobalTheory.HSAmp.continuous_val_and_bounded <;> assumption)
