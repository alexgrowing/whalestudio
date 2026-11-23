import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalListHarishChandraPairingNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidal_list_harishChandra_pairing_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (χ : Gn g n → ℂ), IsIrr χ → ∃ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) ∧ degL L = n ∧ ip χ (hcL L n) ≠ 0 := by
  first | exact @GlobalTheory.GLq.SuppCusp.exists_cusp_list | exact GlobalTheory.GLq.SuppCusp.exists_cusp_list | (intros; apply GlobalTheory.GLq.SuppCusp.exists_cusp_list <;> assumption)
