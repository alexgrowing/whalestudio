import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integers_of_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : Qbar l), MemE c x → ‖x‖ ≤ 1 → x ∈ c.O := by
  first | exact @GlobalTheory.Ord2.mem_coefO_of_memE_norm_le_one | exact GlobalTheory.Ord2.mem_coefO_of_memE_norm_le_one | (intros; apply GlobalTheory.Ord2.mem_coefO_of_memE_norm_le_one <;> assumption)
