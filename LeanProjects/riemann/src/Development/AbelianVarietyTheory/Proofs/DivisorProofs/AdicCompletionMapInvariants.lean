import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapSubApply

namespace GlobalTheory

open AdicCompletion in

theorem adicCompletion_map_invariants : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by
  first
  | exact @_root_.GlobalTheory.LinearMapDifferenceFormula.main
  | exact _root_.GlobalTheory.LinearMapDifferenceFormula.main
  | (apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LinearMapDifferenceFormula.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LinearMapDifferenceFormula.main ..)

end GlobalTheory
