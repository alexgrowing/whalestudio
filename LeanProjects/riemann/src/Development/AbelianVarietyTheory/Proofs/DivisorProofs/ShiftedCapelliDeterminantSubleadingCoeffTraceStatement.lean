import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace
import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_capelli_determinant_subleading_coeff_trace : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ), ∃ (c : ℕ → A) (t : ℂ),
    c (m + 1) = 1 ∧ c m = ∑ i, E i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  first | exact @GlobalTheory.CapelliNext.qdet_shift_next_coeff | exact GlobalTheory.CapelliNext.qdet_shift_next_coeff | (intros; apply GlobalTheory.CapelliNext.qdet_shift_next_coeff <;> assumption)
