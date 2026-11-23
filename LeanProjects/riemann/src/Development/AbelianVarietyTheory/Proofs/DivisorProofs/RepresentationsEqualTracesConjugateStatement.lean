import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationsEqualTracesConjugate
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representations_equal_traces_conjugate : ∀ (I : Type) [Fintype I] [DecidableEq I] (m g : ℕ), 0 < m → ∀ (σ σ' : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ), (∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ x, σ' x * h = h * σ x := by
  first | exact @GlobalTheory.conj_of_trace_central_idem_eq | exact GlobalTheory.conj_of_trace_central_idem_eq | (intros; apply GlobalTheory.conj_of_trace_central_idem_eq <;> assumption)
