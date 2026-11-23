import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierMonomialMemRadicalExtendedMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierMonomial_mem_radical_extended_maximalIdeal : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 3 ≤ N₁ → Φ.Exact N₁ → ∀ (y : Φ.Y) (nu : Fin s → Φ.X y), nu ≠ 0 → mono W (Φ.t y) (Φ.δ y) nu ∈ ((maximalIdeal A).map (Φ.ev y)).radical := by
  first | exact @GlobalTheory.Poinc.RadQ.mono_mem_radical | exact GlobalTheory.Poinc.RadQ.mono_mem_radical | (intros; apply GlobalTheory.Poinc.RadQ.mono_mem_radical <;> assumption)
