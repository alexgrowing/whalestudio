import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisIncl
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 ↔ ∃ w, crisIncl P ℚ_[l] V w = z := by
  first | exact @GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl | exact GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl | (intros; apply GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl <;> assumption)
