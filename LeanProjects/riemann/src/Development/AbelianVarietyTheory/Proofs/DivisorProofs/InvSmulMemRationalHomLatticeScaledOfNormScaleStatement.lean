import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvSmulMemRationalHomLatticeScaledOfNormScale
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB

open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ), cc ≠ ⊥ → GlobalTheory.NormExact.IsScale D cc r → ∀ z ∈ GlobalTheory.InertSign.RL D cc (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d), r⁻¹ • z ∈ GlobalTheory.InertSign.RL D D.host.ccK (GlobalTheory.VacRead.lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  first | exact @GlobalTheory.VacRead.rl_div_scale | exact GlobalTheory.VacRead.rl_div_scale | (intros; apply GlobalTheory.VacRead.rl_div_scale <;> assumption)
