import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveCocycleLocalTrivial
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_cocycle_local_trivial : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ H : Fl g → Pt E g → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (H l) (cov U g)) → (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, H (l + l') P = H l (transl τ l' P) + H l' P) → ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ, DifferentiableOn ℂ K (cov V g) ∧ ∀ i : Fin g, ∀ P ∈ cov V g, H (Pi.single (Sum.inr i) (1 : ℝ)) P = K (transl τ (Pi.single (Sum.inr i) (1 : ℝ)) P) - K P := by
  first | exact @GlobalTheory.RealTranslCob.main | exact GlobalTheory.RealTranslCob.main | (intros; apply GlobalTheory.RealTranslCob.main <;> assumption)
