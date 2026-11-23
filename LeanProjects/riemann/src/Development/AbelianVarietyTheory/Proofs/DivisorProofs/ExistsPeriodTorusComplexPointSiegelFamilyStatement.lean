import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodTorusComplexPointSiegelFamily
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodTorus_complexPoint_siegelFamily : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → ∃ τ : Matrix (Fin h) (Fin h) ℂ, PtAt F.univ p τ := by
  first | exact @GlobalTheory.SiegelPtAt.exists_ptAt | exact GlobalTheory.SiegelPtAt.exists_ptAt | (intros; apply GlobalTheory.SiegelPtAt.exists_ptAt <;> assumption)
