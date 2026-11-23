import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.Restricted

open GroundTheory.Automorphic.RestrictedTensor
open scoped TensorProduct

namespace PositivityTheory.TfC.OccursIff.Span

theorem span_core {ι : Type} {W : ι → Type} [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)] (ξ : ∀ v, W v)
    {C W₁ W₂ H : Type} [AddCommGroup C] [Module ℂ C] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂]
    [Module ℂ W₂] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : C ≃ₗ[ℂ] W₁ ⊗[ℂ] W₂)
    (Te : W₂ ≃ₗ[ℂ] restrictedTensor ξ) (Φ : C →ₗ[ℂ] H) (u : H)
    (h : ∀ a (x : ∀ v, W v) (hx : IsRestricted ξ x),
      inner ℂ (Φ (E.symm (a ⊗ₜ Te.symm ⟨PiTensorProduct.tprod ℂ x, tprod_mem_restrictedTensor hx⟩))) u = 0)
    (c : C) : inner ℂ (Φ c) u = 0 := by
  let Z : Submodule ℂ C :=
    { carrier := {c | inner ℂ (Φ c) u = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, inner_add_left, ha, hb, add_zero]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [map_zero, inner_zero_left]
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_smul, inner_smul_left, hx, mul_zero] }
  have hZ : ∀ c, c ∈ Z ↔ inner ℂ (Φ c) u = 0 := fun c => Iff.rfl
  have h2 : ∀ a (r : restrictedTensor ξ), E.symm (a ⊗ₜ Te.symm r) ∈ Z := by
    intro a r
    obtain ⟨r, hr⟩ := r
    induction hr using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        exact (hZ _).2 (h a x hx)
    | zero =>
        have e : (⟨0, Submodule.zero_mem _⟩ : restrictedTensor ξ) = 0 := rfl
        rw [e, map_zero, TensorProduct.tmul_zero, map_zero]
        exact Z.zero_mem
    | add y z hy hz ihy ihz =>
        have e : (⟨y + z, add_mem hy hz⟩ : restrictedTensor ξ) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
        rw [e, map_add, TensorProduct.tmul_add, map_add]
        exact Z.add_mem ihy ihz
    | smul c y hy ihy =>
        have e : (⟨c • y, Submodule.smul_mem _ c hy⟩ : restrictedTensor ξ) = c • ⟨y, hy⟩ := rfl
        rw [e, map_smul, TensorProduct.tmul_smul, map_smul]
        exact Z.smul_mem c ihy
  have h3 : ∀ t : W₁ ⊗[ℂ] W₂, E.symm t ∈ Z := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Z.zero_mem
    | tmul a b =>
        have := h2 a (Te b)
        rwa [LinearEquiv.symm_apply_apply] at this
    | add s t hs ht => rw [map_add]; exact Z.add_mem hs ht
  have := h3 (E c)
  rwa [LinearEquiv.symm_apply_apply] at this

end PositivityTheory.TfC.OccursIff.Span
