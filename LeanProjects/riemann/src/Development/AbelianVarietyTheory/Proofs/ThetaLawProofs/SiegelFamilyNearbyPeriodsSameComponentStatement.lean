import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponent
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_nearbyPeriods_same_component : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ₀ : Matrix (Fin h) (Fin h) ℂ) (p₀ : Sp ℂ ⟶ F.X), p₀ ≫ F.s = spMap σ → PtAt F.univ p₀ τ₀ → ∃ N ∈ nhds τ₀, ∀ τ ∈ N, ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → PtAt F.univ p τ → SameComp F.s σ p p₀ := by
  first | exact @GlobalTheory.SiegelNearby.exists_nhds_sameComp | exact GlobalTheory.SiegelNearby.exists_nhds_sameComp | (intros; apply GlobalTheory.SiegelNearby.exists_nhds_sameComp <;> assumption)
