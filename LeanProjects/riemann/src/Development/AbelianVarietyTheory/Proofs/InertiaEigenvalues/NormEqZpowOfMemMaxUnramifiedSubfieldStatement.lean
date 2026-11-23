import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_zpow_of_mem_maxUnramifiedSubfield : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : Om l), x ∈ K0 K → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by
  first | exact @GlobalTheory.UnramValue.norm_of_mem_unramified_subfield | exact GlobalTheory.UnramValue.norm_of_mem_unramified_subfield | (intros; apply GlobalTheory.UnramValue.norm_of_mem_unramified_subfield <;> assumption)
