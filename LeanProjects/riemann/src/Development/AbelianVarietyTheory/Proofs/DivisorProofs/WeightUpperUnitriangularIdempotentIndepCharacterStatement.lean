import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightUpperUnitriangularIdempotentIndepCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_upperUnitriangularIdempotent_indep_character : ∀ (D : D7) (k : Fin 2) (ψ ψ' : AddChar (ZMod (D.host.g k)) ℂ), ψ ≠ 1 → ψ' ≠ 1 → ∀ f, wtOf D k (eUk D k ψ) f = wtOf D k (eUk D k ψ') f := by
  first | exact @GlobalTheory.BadCount.wtOf_eUk_indep | exact GlobalTheory.BadCount.wtOf_eUk_indep | (intros; apply GlobalTheory.BadCount.wtOf_eUk_indep <;> assumption)
