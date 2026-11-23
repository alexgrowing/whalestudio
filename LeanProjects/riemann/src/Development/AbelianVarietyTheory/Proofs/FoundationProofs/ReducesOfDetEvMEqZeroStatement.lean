import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesOfDetEvMEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduces_of_det_evM_eq_zero' : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (τ₀ : ℍ), IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (evM s w F τ₀).det = 0 → Reduces Γ w F := by
  first | exact @GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero | exact GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero | (intros; apply GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero <;> assumption)
