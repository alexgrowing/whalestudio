import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalBlockAverageLastColumnEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import GroundTheory.GlobalFields.TateThesis.AdelicChar
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_blockAverage_lastColumn_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspRep.IsCuspidal F → ∀ r : ℕ, 0 < r → r ≤ a - 1 → ∀ g : GA E a, GlobalTheory.CuspGeneric.avg (GlobalTheory.CuspGeneric.ratV E (GlobalTheory.CuspGeneric.UnipotentBlockColumnIndex a r (a - 1))) (fun x => F ((GlobalTheory.CuspGeneric.blkU x : GA E a) * g)) = 0 := by
  first | exact @GlobalTheory.CuspGeneric.avg_blk_last_eq_zero | exact GlobalTheory.CuspGeneric.avg_blk_last_eq_zero | (intros; apply GlobalTheory.CuspGeneric.avg_blk_last_eq_zero <;> assumption)
