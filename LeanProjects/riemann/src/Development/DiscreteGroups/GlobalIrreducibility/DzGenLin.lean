import Mathlib

namespace DiscreteGroups.sglob.DzType

theorem exists_functional_of_finite {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (N : Set G) (θ : G → ℂ) (v : X)
    (h : ∀ F : Finset G, (↑F ⊆ N) →
      ∃ Λ : Module.Dual ℂ X, (∀ u ∈ F, ∀ x, Λ (ρ u x) = θ u * Λ x) ∧ Λ v ≠ 0) :
    ∃ l : Module.Dual ℂ X, (∀ u ∈ N, ∀ x, l (ρ u x) = θ u * l x) ∧ l v ≠ 0 := by
  classical
  set S : Set X := {y | ∃ u ∈ N, ∃ x, y = ρ u x - θ u • x} with hSdef
  set T : Submodule ℂ X := Submodule.span ℂ S with hTdef
  have hv : v ∉ T := by
    intro hvT
    obtain ⟨A, hA, hvA⟩ := Submodule.mem_span_finite_of_mem_span hvT
    let f : X → G := fun t => if h : ∃ u ∈ N, ∃ x, t = ρ u x - θ u • x then h.choose else 1
    have hf : ∀ t ∈ A, f t ∈ N ∧ ∃ x, t = ρ (f t) x - θ (f t) • x := by
      intro t ht
      have h' : ∃ u ∈ N, ∃ x, t = ρ u x - θ u • x := hA ht
      simp only [f, dif_pos h']
      exact ⟨h'.choose_spec.1, h'.choose_spec.2⟩
    obtain ⟨Λ, hΛ, hΛv⟩ := h (A.image f) (by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      exact (hf t ht).1)
    apply hΛv
    have hle : Submodule.span ℂ (↑A : Set X) ≤ LinearMap.ker Λ := by
      rw [Submodule.span_le]
      intro t ht
      obtain ⟨-, x, hx⟩ := hf t ht
      rw [SetLike.mem_coe, LinearMap.mem_ker, hx, map_sub, map_smul,
        hΛ _ (Finset.mem_image_of_mem f ht) x, smul_eq_mul, sub_self]
    exact hle hvA
  have hq : T.mkQ v ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (X ⧸ T), φ (T.mkQ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  refine ⟨φ ∘ₗ T.mkQ, fun u hu x => ?_, hφ⟩
  have hmem : ρ u x - θ u • x ∈ T := Submodule.subset_span ⟨u, hu, x, rfl⟩
  have h0 : (φ ∘ₗ T.mkQ) (ρ u x - θ u • x) = 0 := by
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T).2 hmem, map_zero]
  set l := φ ∘ₗ T.mkQ
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0

end DiscreteGroups.sglob.DzType
