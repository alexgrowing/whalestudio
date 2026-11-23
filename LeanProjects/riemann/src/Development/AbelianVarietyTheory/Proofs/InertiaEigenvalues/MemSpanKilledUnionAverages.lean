import Mathlib

namespace GlobalTheory

private theorem exists_equivariant_projection_onto_invariant_submodule {G M : Type} [Group G] [Fintype G] [AddCommGroup M]
    [Module ℂ M] (S W : Submodule ℂ M) (π : G → Module.End ℂ M)
    (h1 : ∀ v ∈ S, π 1 v = v)
    (hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v))
    (hWS : W ≤ S) (hW : ∀ g, ∀ w ∈ W, π g w ∈ W) :
    ∃ P : M →ₗ[ℂ] M, (∀ x, P x ∈ W) ∧ (∀ w ∈ W, P w = w) ∧
      (∀ g, ∀ x ∈ S, P (π g x) = π g (P x)) := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl W
  refine ⟨(Fintype.card G : ℂ)⁻¹ • ∑ g, π g⁻¹ ∘ₗ W.projection q hq ∘ₗ π g,
    ?_, ?_, ?_⟩
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    exact W.smul_mem _ (W.sum_mem fun g _ => hW _ _ (Submodule.projection_apply_mem _ _))
  · intro w hw
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    have key : ∀ g : G, π g⁻¹ (W.projection q hq (π g w)) = w := by
      intro g
      rw [Submodule.projection_apply_of_mem_left hq (hW g w hw), ← hmul _ _ w (hWS hw)]
      simp [h1 w (hWS hw)]
    simp only [key, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
  · intro h x hx
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    refine congrArg (fun y => (Fintype.card G : ℂ)⁻¹ • y) ?_
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft]
    rw [← hmul _ _ x hx, ← hmul _ h _ (hWS (Submodule.projection_apply_mem _ _))]
    simp only [mul_inv_rev, inv_mul_cancel_right]

theorem mem_span_killed_union_averages {G M : Type} [Group G] [Fintype G] [AddCommGroup M]
    [Module ℂ M] (S : Submodule ℂ M) (π : G → Module.End ℂ M)
    (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) (h1 : ∀ v ∈ S, π 1 v = v)
    (hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v))
    (C : Set (G → ℂ)) (hC : ∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C)
    (v : M) (hv : v ∈ S) :
    v ∈ Submodule.span ℂ ({w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} ∪
      {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}) := by
  classical
  have hAS : ∀ (c : G → ℂ), ∀ w ∈ S, ∑ g, c g • π g w ∈ S := fun c w hw =>
    S.sum_mem fun g _ => S.smul_mem _ (hS g w hw)
  have hWS : Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} ≤ S :=
    Submodule.span_le.2 (by rintro u ⟨c, -, w, hw, rfl⟩; exact hAS c w hw)
  have hWst : ∀ h, ∀ u ∈ Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w},
      π h u ∈ Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} := by
    intro h u hu
    have hle : Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} ≤
        (Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}).comap (π h) := by
      refine Submodule.span_le.2 ?_
      rintro u ⟨c, hc, w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.subset_span ⟨fun k => c (h * k * h⁻¹), hC c hc h, π h w, hS h w hw, ?_⟩
      rw [map_sum]
      refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv,
        map_smul]
      rw [show h * (h⁻¹ * g * h) * h⁻¹ = g by group, ← hmul _ _ w hw, ← hmul _ _ w hw,
        show g * h = h * (h⁻¹ * g * h) by group]
    exact hle hu
  obtain ⟨P, hPW, hPid, hPc⟩ := exists_equivariant_projection_onto_invariant_submodule S _ π h1 hmul hWS hWst
  have hPv : P v ∈ S := hWS (hPW v)
  have hPc' : ∀ g, P (π g v) = π g (P v) := fun g => hPc g v hv
  have hkill : v - P v ∈ {w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} := by
    refine ⟨S.sub_mem hv hPv, fun c hc => ?_⟩
    have hA : ∑ g, c g • π g (P v) = P (∑ g, c g • π g v) := by
      simp only [map_sum, map_smul, hPc']
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib, hA]
    rw [hPid _ (Submodule.subset_span ⟨c, hc, v, hv, rfl⟩), sub_self]
  have hsum := Submodule.add_mem _ (Submodule.subset_span (Set.mem_union_left _ hkill))
    (Submodule.span_mono Set.subset_union_right (hPW v))
  rwa [sub_add_cancel] at hsum

end GlobalTheory
