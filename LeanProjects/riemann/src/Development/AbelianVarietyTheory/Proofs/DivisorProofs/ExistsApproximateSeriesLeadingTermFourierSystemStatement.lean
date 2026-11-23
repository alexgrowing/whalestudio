import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximateSeriesLeadingTermFourierSystem
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approximate_series_leading_term_fourierSystem : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O), BddAct bar → ∀ (q : ℕ) (φ : InvFun O), IsPolFan bar q φ → ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (N₁ : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y₀ : Φ.Y) (γ : Fin (Φ.m y₀) → LinearMap.BilinForm ℤ (Φ.X y₀)) (M : ℕ), 1 ≤ M → (∀ i, Φ.δ y₀ i = (M : ℤ) • γ i) → ∀ (d l : ℕ) (a : Fin l × Fin s → Φ.X y₀), Dominant bar φ d N₁ W γ a → ∀ (c : Fin l → Φ.Q) (e : ℕ), ∃ f : A, Φ.OrdGe φ d e f ∧ Φ.Leads y₀ a c e f := by
  first | exact @GlobalTheory.Poinc.approx_of_vsys | exact GlobalTheory.Poinc.approx_of_vsys | (intros; apply GlobalTheory.Poinc.approx_of_vsys <;> assumption)
