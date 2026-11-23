import Mathlib

namespace GlobalTheory

def UnramSub {V F : Type} [CommRing V] [Field F] (i : V →+* F) (T : Subring F) : Prop :=
  ∃ (_ : IsDiscreteValuationRing T) (f : V →+* T), (∀ v, (f v : F) = i v) ∧ ∀ π : V, Irreducible π → Irreducible (f π)

namespace UnramSub

variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}

theorem mem {T : Subring F} (h : UnramSub i T) (v : V) : i v ∈ T := by
  obtain ⟨_, f, hf, -⟩ := h
  exact hf v ▸ (f v).2

theorem isDVR {T : Subring F} (h : UnramSub i T) : IsDiscreteValuationRing T := h.1

theorem trans {T₁ T₂ : Subring F} (h₁ : UnramSub i T₁) (h₂ : UnramSub T₁.subtype T₂) : UnramSub i T₂ := by
  obtain ⟨_, f₁, hf₁, hi₁⟩ := h₁
  obtain ⟨_, f₂, hf₂, hi₂⟩ := h₂
  refine ⟨‹_›, f₂.comp f₁, fun v => ?_, fun π hπ => hi₂ _ (hi₁ π hπ)⟩
  rw [RingHom.comp_apply, hf₂, Subring.coe_subtype, hf₁]

theorem le {T₁ T₂ : Subring F} (h₂ : UnramSub T₁.subtype T₂) : T₁ ≤ T₂ := fun z hz => h₂.mem ⟨z, hz⟩

theorem range [IsDomain V] [IsDiscreteValuationRing V] (hi : Function.Injective i) : UnramSub i i.range := by
  let e : V ≃+* i.range := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hi)
  exact ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, e.toRingHom, fun v => rfl,
    fun π hπ => hπ.map e⟩

end UnramSub

end GlobalTheory
