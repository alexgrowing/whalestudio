import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosInnerEqShiftedOuter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_windowZeros_inner_eq_shifted_outer : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F), ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F, Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} = Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  first | exact @GlobalTheory.PMonE.win_inner | exact GlobalTheory.PMonE.win_inner | (intros; apply GlobalTheory.PMonE.win_inner <;> assumption)
