import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def placesRing {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) : Subring L where
  carrier := {x | ∀ w ∈ S, w x ≤ 1}
  zero_mem' := fun w _ ↦ by simp
  one_mem' := fun w _ ↦ by simp
  add_mem' := fun hx hy w hw ↦ (FinitePlace.add_le w _ _).trans (max_le (hx w hw) (hy w hw))
  neg_mem' := fun hx w hw ↦ by simpa [map_neg_eq_map] using hx w hw
  mul_mem' := fun hx hy w hw ↦ by
    rw [map_mul]
    exact mul_le_one₀ (hx w hw) (apply_nonneg w _) (hy w hw)

theorem mem_placesRing {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) (x : L) :
    x ∈ placesRing S ↔ ∀ w ∈ S, w x ≤ 1 := Iff.rfl

example {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) (x : 𝓞 L) :
    algebraMap (𝓞 L) L x ∈ placesRing S := fun w _ ↦ by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_le_one _ _ x

example : placesRing (∅ : Set (FinitePlace ℚ)) = ⊤ :=
  eq_top_iff.2 fun _ _ w hw ↦ absurd hw (Set.notMem_empty w)

end GroundTheory.Heights₂.Heights
