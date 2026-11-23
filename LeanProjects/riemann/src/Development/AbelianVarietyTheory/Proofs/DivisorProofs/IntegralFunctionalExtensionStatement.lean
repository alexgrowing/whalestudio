import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFunctionalExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_functional_extension : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (X : Type) [AddCommGroup X] [Module C X] [Module O X] [IsScalarTower O C X] (L : Submodule O X) (S : Submodule C X) (f : X →ₗ[C] C), v.Integers O → L.FG → (∀ x ∈ L, x ∈ S → f x ∈ (algebraMap O C).range) → ∃ F : X →ₗ[C] C, (∀ x ∈ L, F x ∈ (algebraMap O C).range) ∧ ∀ x ∈ L, x ∈ S → F x = f x := by
  first | exact @GlobalTheory.integral_form_extend_of_saturated | exact GlobalTheory.integral_form_extend_of_saturated | (intros; apply GlobalTheory.integral_form_extend_of_saturated <;> assumption)
