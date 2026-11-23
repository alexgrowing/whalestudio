import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_action_factors (k : Type) [Field k] (C O B : Type) [CommRing C] [Ring O] [Algebra C O]
    [Algebra C k] [Ring B] [Algebra k B] (e : (k ⊗[C] O) ≃ₐ[k] B) (X : Type) [AddCommGroup X]
    [Module k X] (σX : O →+* Module.End k X)
    (hσ : ∀ c, σX (algebraMap C O c) = algebraMap C k c • 1) :
    ∃ ρX : B →ₐ[k] Module.End k X, ∀ o, ρX (e (1 ⊗ₜ[C] o)) = σX o := by
  letI : Algebra C (Module.End k X) :=
    ((algebraMap k (Module.End k X)).comp (algebraMap C k)).toAlgebra'
      (fun c f => Algebra.commutes (algebraMap C k c) f)
  haveI : IsScalarTower C k (Module.End k X) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : O →ₐ[C] Module.End k X :=
    { σX with
      commutes' := fun c => by
        change σX (algebraMap C O c) = algebraMap k (Module.End k X) (algebraMap C k c)
        rw [hσ]; exact (Algebra.algebraMap_eq_smul_one _).symm }
  let F : (k ⊗[C] O) →ₐ[k] Module.End k X :=
    Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k X)) g
      (fun x y => Algebra.commutes x (g y))
  refine ⟨F.comp e.symm.toAlgHom, fun o => ?_⟩
  show F (e.symm (e (1 ⊗ₜ[C] o))) = σX o
  rw [e.symm_apply_apply]
  rw [show F (1 ⊗ₜ[C] o) = Algebra.ofId k (Module.End k X) 1 * g o from
    Algebra.TensorProduct.lift_tmul _ _ _ _ _, map_one, one_mul]
  rfl

end GlobalTheory
