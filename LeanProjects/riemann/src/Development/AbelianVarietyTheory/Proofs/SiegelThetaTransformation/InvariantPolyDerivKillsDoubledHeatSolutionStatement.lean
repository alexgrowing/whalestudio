import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolyDerivKillsDoubledHeatSolution
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_polyDeriv_kills_doubled_heat_solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), r ≤ n → InvFam P → ∀ D : CM X.Ψ r r → CM X.Ψ n r → CM X.Ψ n r → ℂ, IsHeat X.Ψ D → (∀ Z ∈ Hn X.Ψ r, D Z 0 0 = 0) → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, biDeriv X hr idx P (fun z₁ w => kZero X idx x₁ x₂ z₁ w * D (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) = 0 := by
  first | exact @GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | exact GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | (intros; apply GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero <;> assumption)
