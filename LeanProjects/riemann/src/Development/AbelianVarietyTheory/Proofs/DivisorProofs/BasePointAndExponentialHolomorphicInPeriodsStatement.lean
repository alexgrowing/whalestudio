import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePointAndExponentialHolomorphicInPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basePoint_and_exponential_holomorphic_in_periods : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), 3 ≤ N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → C D' t → FullMark N D' t → IsOpen B → IsHolPeriods D' ρ B P → (∀ b ∈ B, UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b)) → IsHolTo B y ∧ IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
  first | exact @GlobalTheory.PELUHol.isHolTo_point_and_exp | exact GlobalTheory.PELUHol.isHolTo_point_and_exp | (intros; apply GlobalTheory.PELUHol.isHolTo_point_and_exp <;> assumption)
