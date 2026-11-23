import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackForm
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_coords_symplectic_pullback_form : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ γ : Sp g, ∀ P ∈ cov B g, flat (fun b => moeb γ (τ b)) (reframe τ γ P) = flat τ P ᵥ* (γ⁻¹).mat ∧ pull (reframe τ γ) (om0 fun b => moeb γ (τ b)) P = om0 τ P := by
  first | exact @GlobalTheory.sympFlat_change | exact GlobalTheory.sympFlat_change | (intros; apply GlobalTheory.sympFlat_change <;> assumption)
