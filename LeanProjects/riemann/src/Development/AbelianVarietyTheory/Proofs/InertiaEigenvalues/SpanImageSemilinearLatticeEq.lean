import Mathlib
open NumberField

namespace GlobalTheory

theorem span_image_span_eq_of_integral (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O]
    (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V']
    [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V')
    (he : ∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) (S : Set V) :
    Submodule.span O (iV '' (Submodule.span (𝓞 K) S : Set V)) = Submodule.span O (iV '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨z, hz⟩ := he a
      have h1 : a • x = ((a : K)) • x := (algebraMap_smul K a x).symm
      rw [h1, LinearMap.map_smulₛₗ, ← hz, algebraMap_smul]
      exact Submodule.smul_mem _ z hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

end GlobalTheory
