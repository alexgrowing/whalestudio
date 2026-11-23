import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarmonicColumnOperatorEndMemOfUnitaryStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumSmulMemOfSumZpowSmulMem
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicColumnOperatorEnd_mem_of_unitary_stable : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {p q n : ℕ} (W : Submodule ℂ (GlobalTheory.Harm.Poly ℂ ι p q (Fin n))), (∀ g : ι → GL (Fin n) ℂ, (∀ t, (g t : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ w ∈ W, GlobalTheory.Harm.colActHom g w ∈ W) → ∀ (t : ι) (k l : Fin n), ∀ w ∈ W, GlobalTheory.Harm.colLie ℂ p q t k l w ∈ W := by
  first | exact @GlobalTheory.Harm.colLie_mem_of_unitary_stable | exact GlobalTheory.Harm.colLie_mem_of_unitary_stable | (intros; apply GlobalTheory.Harm.colLie_mem_of_unitary_stable <;> assumption)
