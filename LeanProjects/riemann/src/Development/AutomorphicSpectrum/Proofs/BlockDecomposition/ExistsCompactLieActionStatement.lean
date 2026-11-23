import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieAction
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_lie_action : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)), Continuous ρ → (∀ k v, ‖ρ k v‖ = ‖v‖) → ∃ G : Fin n → Fin n → Module.End ℂ H, Formalism.REAL.GlRel G ∧ (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) ∧ (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep | exact GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep | (intros; apply GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep <;> assumption)
