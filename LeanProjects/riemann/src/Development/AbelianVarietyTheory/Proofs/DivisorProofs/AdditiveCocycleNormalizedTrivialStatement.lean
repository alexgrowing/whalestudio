import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveCocycleNormalizedTrivial
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_cocycle_normalized_trivial : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ H : Fl g → Pt E g → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (H l) (cov U g)) → (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, H (l + l') P = H l (transl τ l' P) + H l' P) → (∀ i : Fin g, ∀ P ∈ cov U g, H (Pi.single (Sum.inr i) (1 : ℝ)) P = 0) → ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ, DifferentiableOn ℂ K (cov V g) ∧ ∃ μ : Fl g → E → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (μ l) V) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b' ∈ V, μ (l + l') b' = μ l b' + μ l' b') ∧ ∀ l ∈ stdLat g, ∀ P ∈ cov V g, H l P = K (transl τ l P) - K P + μ l P.1 := by
  first | exact @GlobalTheory.PeriodCocycle.exists_coboundary_add_char | exact GlobalTheory.PeriodCocycle.exists_coboundary_add_char | (intros; apply GlobalTheory.PeriodCocycle.exists_coboundary_add_char <;> assumption)
