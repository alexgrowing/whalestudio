import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDifferentLatticeProductHermitianIsSelfDual
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB

open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ), cc ≠ ⊥ → GlobalTheory.NormExact.IsScale D cc r → Formalism.MainNotions.StandardLatticesGL3.SD D (GlobalTheory.VacRead.lsB D cc r a) := by
  first | exact @GlobalTheory.VacRead.lsB_selfDual | exact GlobalTheory.VacRead.lsB_selfDual | (intros; apply GlobalTheory.VacRead.lsB_selfDual <;> assumption)
