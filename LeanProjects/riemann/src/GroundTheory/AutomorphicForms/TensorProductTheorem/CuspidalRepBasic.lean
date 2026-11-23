import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep

namespace GroundTheory.Automorphic

namespace AutomorphicForm

namespace CuspidalAutomorphicRepresentation

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

@[ext] theorem ext {π π' : CuspidalAutomorphicRepresentation K n} (h : π.carrier = π'.carrier) : π = π' := by
  cases π
  cases π'
  subst h
  rfl

theorem carrier_ne_bot (π : CuspidalAutomorphicRepresentation K n) : π.carrier ≠ ⊥ := by
  intro h
  have hirr : IsSimpleOrder (Subrepresentation π.toModule.fullRep) := π.isIrreducible
  apply (bot_ne_top : (⊥ : Subrepresentation π.toModule.fullRep) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  show (⊥ : Submodule ℂ π.carrier) = ⊤
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (x : cuspForms K n) ∈ (⊥ : Submodule ℂ (cuspForms K n)) := h ▸ x.2
  rw [Submodule.mem_bot] at hx ⊢
  exact Subtype.ext hx

theorem exists_mem_ne_zero (π : CuspidalAutomorphicRepresentation K n) : ∃ φ ∈ π.carrier, φ ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot π.carrier_ne_bot

end CuspidalAutomorphicRepresentation

end AutomorphicForm

end GroundTheory.Automorphic
