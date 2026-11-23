import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOneAddPrimePowMulNotRootOfUnity
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_one_add_primePow_mul_not_rootOfUnity : ∀ (l : ℕ) [Fact l.Prime] (a : ℂ_[l]), a ≠ 0 → ∃ k : ℕ, 1 + (l : ℂ_[l]) ^ k * a ≠ 0 ∧ ∀ i : ℕ, 1 ≤ i → (1 + (l : ℂ_[l]) ^ k * a) ^ i ≠ 1 := by
  first | exact @GlobalTheory.SmallRootCl.exists_one_add_pow_mul_not_root | exact GlobalTheory.SmallRootCl.exists_one_add_pow_mul_not_root | (intros; apply GlobalTheory.SmallRootCl.exists_one_add_pow_mul_not_root; all_goals assumption)
