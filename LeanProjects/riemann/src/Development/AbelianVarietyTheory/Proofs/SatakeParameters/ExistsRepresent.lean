import Mathlib

namespace GlobalTheory.ExistsRepresentation

theorem exists_represent {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v : V, v ≠ 0 → (0 : ℝ) < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  classical
  let b := Module.finBasis ℂ W
  let Φ : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun u i => Bf (u : V) (b i : V)
      map_add' := by
        intro u u'
        funext i
        simp
      map_smul' := by
        intro c u
        funext i
        simp }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hall : ∀ w : W, Bf (u : V) (w : V) = 0 := by
      intro w
      rw [← b.sum_repr w]
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smulₛₗ]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have h0 := congrFun hu i
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      simp [h0]
    by_contra hne
    have hne' : (u : V) ≠ 0 := by simpa using hne
    have h1 := hpos _ hne'
    rw [hall u] at h1
    simp at h1
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  obtain ⟨u, hu⟩ := hsurj (fun i => L (b i : V))
  refine ⟨u, u.2, fun w hw => ?_⟩
  have hwsum : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V) := by
    have h2 := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  rw [hwsum]
  simp only [map_sum, map_smulₛₗ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h3 := congrFun hu i
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h3
  rw [h3]

end GlobalTheory.ExistsRepresentation
