import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisDivisibleOfKernelPowers
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_divisible_of_kernel_powers : ∀ (l : ℕ) [Fact l.Prime], ∀ s : Per.Acris0 l, (∀ n : ℕ, ∃ (u w : Per.Acris0 l), s = u + (l : Per.Acris0 l) * w ∧ (u : Per.AinfP l) ∈ Per.kerP l ^ n) → (l : Per.Acris0 l) ∣ s := by
  first | exact @GlobalTheory.MemLoc.dvd_of_forall_fil_add | exact GlobalTheory.MemLoc.dvd_of_forall_fil_add | (intros; apply GlobalTheory.MemLoc.dvd_of_forall_fil_add <;> assumption)
