import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareApproxValuesAtPointOfElements
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareApprox_values_at_point_of_elements : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (q : ℕ) (φ : InvFun O), IsPolFan bar q φ → NoSelfInt bar q φ → ∀ d₀ d : ℕ, 1 ≤ d₀ → 1 ≤ d → HasSupports bar q φ d₀ → ∀ (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ), PosW W → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ (A : Type) [CommRing A] [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) (ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y)) (M : ℕ), 1 ≤ M → IsCone bar φ ga → (∀ k, Φ.δ y k = (M : ℤ) • ga k) → ∀ (K : Type) [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K), Elements Φ y φ d ga ev k₀ → Values Φ y ev k₀ := by
  first | exact @GlobalTheory.Poinc.Sep.values_of_elements | exact GlobalTheory.Poinc.Sep.values_of_elements | (intros; apply GlobalTheory.Poinc.Sep.values_of_elements <;> assumption)
