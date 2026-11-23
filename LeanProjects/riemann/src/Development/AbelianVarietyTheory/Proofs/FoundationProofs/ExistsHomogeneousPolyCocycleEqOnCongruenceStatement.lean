import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomogeneousPolyCocycleEqOnCongruence
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence : ∀ (N l w : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ → ∀ n : ℕ, ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z ∧ Near z (Φ n) := by
  first | exact @GlobalTheory.KZ.H3.exists_coc_near | exact GlobalTheory.KZ.H3.exists_coc_near | (intros; apply GlobalTheory.KZ.H3.exists_coc_near <;> assumption)
