import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodTransformationUnitary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_transformation_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dd : Datum H) (g p : ℕ) (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) (ρ : Fin p → Fin g), Function.Injective ρ → (∀ i, ty i = τ ↔ i ∈ Set.range ρ) → ∀ (P P' : Dd.La →+ (Fin g → ℂ)), IsPeriod Dd ty P → IsPeriod Dd ty P' → ∀ (gam : Dd.La ≃ₗ[𝓞 E] Dd.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a, P' (gam a) = h (P a)) → ∃ Hm : Matrix (Fin p) (Fin p) ℂ, IsUnit Hm ∧ ∀ (v : Fin g → ℂ) (a : Fin p), h v (ρ a) = ∑ b, Hm a b * v (ρ b) := by
  first | exact @GlobalTheory.PeriodBlock.exists_block | exact GlobalTheory.PeriodBlock.exists_block | (intros; apply GlobalTheory.PeriodBlock.exists_block <;> assumption)
