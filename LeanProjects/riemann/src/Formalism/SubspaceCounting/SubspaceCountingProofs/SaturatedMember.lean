import Formalism.SubspaceCounting.Statement

namespace Formalism.G0

theorem saturated_member : SaturatedMember := by
  intro O M _ _ _ _ π hπ M' P τ hsat
  have hπτ : π ^ τ ≠ 0 := pow_ne_zero _ hπ
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨⟨_, hxT⟩, hxM'⟩ := hx
    rw [Submodule.ideal_span_singleton_smul] at hxT ⊢
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxT
    have hy : y ∈ M' := hsat _ _ hπτ hxM'
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hy, rfl⟩
  · set N := P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M)
    let f : (M' ⧸ Submodule.comap M'.subtype N) →ₗ[O] (M ⧸ N) :=
      Submodule.mapQ _ _ M'.subtype le_rfl
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
      simp
    exact Module.length_le_of_injective f hf

end Formalism.G0
