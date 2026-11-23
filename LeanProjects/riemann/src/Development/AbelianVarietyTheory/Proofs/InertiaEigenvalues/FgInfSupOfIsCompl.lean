import Mathlib
open NumberField

namespace GlobalTheory

theorem fg_inf_sup_of_isCompl (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A : Submodule (𝓞 K) V) (U U' : Submodule K V) :
    A.FG → IsCompl U U' →
      (U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K))).FG := by
  intro hA h
  let p : V →ₗ[K] V := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U U' h
  let q : V →ₗ[𝓞 K] V := p.restrictScalars (𝓞 K)
  have hpU : ∀ x, p x ∈ U := fun x => (Submodule.linearProjOfIsCompl U U' h x).2
  have hpl : ∀ x ∈ U, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left h ⟨x, hx⟩)
  have hpr : ∀ x ∈ U', p x = 0 := fun x hx => by
    have := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff h).2 hx
    show ((Submodule.linearProjOfIsCompl U U' h x : U) : V) = 0
    exact congrArg Subtype.val this
  have hsub : ∀ x, x - p x ∈ U' := fun x => by
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff h]
    have h1 : p (x - p x) = 0 := by rw [map_sub, hpl _ (hpU x), sub_self]
    have h2 : ((Submodule.linearProjOfIsCompl U U' h (x - p x) : U) : V) = 0 := h1
    exact_mod_cast h2
  have heq : U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) = A.map q := by
    ext x
    constructor
    · rintro ⟨hxU, hx⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
      refine ⟨a, ha, ?_⟩
      change p a = a + u
      have e1 : p (a + u) = a + u := hpl _ hxU
      rw [map_add, hpr u hu, add_zero] at e1
      exact e1
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hpU a, ?_⟩
      refine Submodule.mem_sup.2 ⟨a, ha, p a - a, ?_, by abel⟩
      have := U'.neg_mem (hsub a)
      simpa using this
  rw [heq]
  exact hA.map q

end GlobalTheory
