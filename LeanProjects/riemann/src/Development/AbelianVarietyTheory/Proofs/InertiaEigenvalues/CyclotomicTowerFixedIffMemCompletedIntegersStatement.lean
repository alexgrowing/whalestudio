import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegers
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 → ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by
  first | exact @GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | exact GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | (intros; apply GlobalTheory.CycInvariants.fixed_iff_mem_Ohat <;> assumption)
