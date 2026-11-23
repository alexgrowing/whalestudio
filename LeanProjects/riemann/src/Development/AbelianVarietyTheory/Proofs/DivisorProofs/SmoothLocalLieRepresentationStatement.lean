import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLocalLieRepresentation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_local_lie_representation : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∃ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsLieRep ρ ∧ IsRightDer J s ρ := by
  first | exact @GlobalTheory.TorFin.exists_rightDer_rep | exact GlobalTheory.TorFin.exists_rightDer_rep | (intros; apply GlobalTheory.TorFin.exists_rightDer_rep <;> assumption)
