import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothBaseDimEqPeriodSpaceDim
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothBase_dim_eq_periodSpace_dim : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d d' : ℕ) (D' : PLat O bar) (t : Λ → D'.La), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → C D' t → (∃ P, IsPeriod D' ρ P) → PerCoord D' ρ d' → d = d' := by
  first | exact @GlobalTheory.DimEq.dim_eq | exact GlobalTheory.DimEq.dim_eq | (intros; apply GlobalTheory.DimEq.dim_eq <;> assumption)
