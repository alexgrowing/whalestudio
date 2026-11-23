import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveAndSaturatedOfInjectiveModRegular
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_and_saturated_of_injective_mod_regular' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] (f : R), f ∈ maximalIdeal R → IsSMulRegular B f → ∀ ψ : A →ₐ[R] B, (∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) → a ∈ (Ideal.span {f}).map (algebraMap R A)) → Function.Injective ψ ∧ ∀ b : B, f • b ∈ ψ.range → b ∈ ψ.range := by
  first | exact @GlobalTheory.injective_and_saturated_of_injective_mod_regular | exact GlobalTheory.injective_and_saturated_of_injective_mod_regular | (intros; apply GlobalTheory.injective_and_saturated_of_injective_mod_regular <;> assumption)
