import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsOfInjectiveZmodEtaleSheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf : ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M], (∀ U : Scheme.{0}, Module.Flat (ULift.{1} (ZMod q)) (Sec M U)) ∧ FlatS M := by
  first | (exact @GlobalTheory.EtC.InjFlat.flat_of_injective) | (exact GlobalTheory.EtC.InjFlat.flat_of_injective) | (intros; apply GlobalTheory.EtC.InjFlat.flat_of_injective  <;> assumption)
