import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndE
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F → (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧ ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by
  first | exact @GlobalTheory.Nef.isFF_main | exact GlobalTheory.Nef.isFF_main | (intros; apply GlobalTheory.Nef.isFF_main <;> assumption)
