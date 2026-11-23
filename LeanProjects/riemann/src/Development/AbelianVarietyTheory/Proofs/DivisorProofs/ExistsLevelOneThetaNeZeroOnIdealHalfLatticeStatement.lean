import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelOneThetaNeZeroOnIdealHalfLattice
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelOne_theta_ne_zero_on_ideal_half_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ (w : E) (L : Lt E r), SelfD X L → ∀ x ∈ X.dom, ∀ (𝔪 : Ideal (𝓞 E)) (M : ℕ), 2 ≤ M → 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)} → ∀ ϑ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L ϑ → ϑ ≠ 0 → ∃ u ∈ 𝔪 • L, ϑ (pv X idx x ((M : E)⁻¹ • u)) ≠ 0 := by
  first | exact @GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half | exact GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half | (intros; apply GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half <;> assumption)
