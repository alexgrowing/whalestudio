import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvec
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_matrix_frame_fvec : ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (e : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1)), inWb k r z' → 0 < Tz k r z' → ∃ Q : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ, Q.det ≠ 0 ∧ (∀ (i j : Fin (r + 1)), ∑ d, Q (Fin.castAdd (r + k) i) d * fvec k r z' j (e d) = if i = j then 1 else 0) ∧ ∀ (i : Fin (r + k)) (j : Fin (r + 1)), ∑ d, Q (Fin.natAdd (r + 1) i) d * fvec k r z' j (e d) = 0 := by
  first | exact @GlobalTheory.HatNF.DualFrame.exists_dual_matrix | exact GlobalTheory.HatNF.DualFrame.exists_dual_matrix | (intros; apply GlobalTheory.HatNF.DualFrame.exists_dual_matrix <;> assumption)
