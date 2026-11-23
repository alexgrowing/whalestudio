import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisToBcrisMemFiltrationOfLadicApprox
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O), (∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) → toOB l O x ∈ filO O C m := by
  first | exact @GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx | exact GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx | (intros; apply GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx <;> assumption)
