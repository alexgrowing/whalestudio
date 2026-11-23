import Mathlib

namespace UpperTheory.Reformulated.B.ExistsAverage

private theorem exists_op {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    (ρ : K →* Module.End ℂ M) (H : Subgroup K) [H.Normal] [H.FiniteIndex] :
    ∃ A : M →ₗ[ℂ] M,
      (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, ρ k (A m) = A m) ∧
      (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, A (ρ k m) = A m) ∧
      (∀ m, (∀ k, ρ k m = m) → A m = m) ∧
      (∀ m, m - A m ∈ Submodule.span ℂ {x : M | ∃ k y, x = y - ρ k y}) := by
  classical
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have hc : ((Fintype.card (K ⧸ H) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : ∀ m, (∀ h ∈ H, ρ h m = m) → ∀ g : K, ρ g m = ρ ((g : K ⧸ H).out) m := by
    intro m hm g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, map_mul, Module.End.mul_apply, hm h h.2]
  have hA : ∀ m, (((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, (ρ q.out : M →ₗ[ℂ] M)) m
      = ((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, ρ q.out m := by
    intro m
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
  have hconst : ∀ m : M, ((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ _q : K ⧸ H, m = m := by
    intro m
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  refine ⟨((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, (ρ q.out : M →ₗ[ℂ] M),
    ?_, ?_, ?_, ?_⟩
  · intro m hm k
    rw [hA, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (k : K ⧸ H)) _ _ fun q => ?_
    rw [← Module.End.mul_apply, ← map_mul, key m hm]
    simp
  · intro m hm k
    rw [hA, hA]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulRight (k : K ⧸ H)) _ _ fun q => ?_
    rw [← Module.End.mul_apply, ← map_mul, key m hm]
    simp
  · intro m hm
    rw [hA]
    simp only [hm]
    exact hconst m
  · intro m
    rw [hA]
    nth_rewrite 1 [← hconst m]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    exact Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨_, _, rfl⟩)

private theorem exists_sub {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (ρ : K →* Module.End ℂ M) (hs : ∀ m : M, IsOpen {k : K | ρ k m = m}) (m : M) :
    ∃ H : Subgroup K, H.Normal ∧ H.FiniteIndex ∧ ∀ h ∈ H, ρ h m = m := by
  let S : Subgroup K :=
    { carrier := {k : K | ρ k m = m}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        nth_rewrite 1 [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S (hs m)
  haveI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact ⟨S.normalCore, inferInstance, inferInstance, fun h hh => S.normalCore_le hh⟩

theorem exists_avg {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (ρ : K →* Module.End ℂ M) (hs : ∀ m : M, IsOpen {k : K | ρ k m = m}) :
    ∃ P : M →ₗ[ℂ] M, (∀ (m : M) (k : K), ρ k (P m) = P m) ∧
      (∀ m : M, (∀ k : K, ρ k m = m) → P m = m) ∧
      ∀ T : M →ₗ[ℂ] M, (∀ (k : K) (m : M), T (ρ k m) = ρ k (T m)) →
        ∀ m : M, T (P m) = P (T m) := by
  set N : Submodule ℂ M := Submodule.span ℂ {x : M | ∃ k y, x = y - ρ k y} with hN
  have hdis : ∀ x ∈ N, (∀ k, ρ k x = x) → x = 0 := by
    intro x hx hfix
    have : ∃ H : Subgroup K, H.Normal ∧ H.FiniteIndex ∧ ∀ A : M →ₗ[ℂ] M,
        (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, A (ρ k m) = A m) → A x = 0 := by
      clear hfix
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, y, rfl⟩ := hx
        obtain ⟨H, h1, h2, h3⟩ := exists_sub ρ hs y
        exact ⟨H, h1, h2, fun A hA => by rw [map_sub, hA y h3, sub_self]⟩
      | zero => exact ⟨⊤, inferInstance, inferInstance, fun A _ => map_zero A⟩
      | add x y _ _ hx hy =>
        obtain ⟨H, h1, h2, h3⟩ := hx
        obtain ⟨H', h1', h2', h3'⟩ := hy
        refine ⟨H ⊓ H', inferInstance, inferInstance, fun A hA => ?_⟩
        rw [map_add, h3 A fun m hm => hA m fun h hh => hm h hh.1,
          h3' A fun m hm => hA m fun h hh => hm h hh.2, add_zero]
      | smul c x _ hx =>
        obtain ⟨H, h1, h2, h3⟩ := hx
        exact ⟨H, h1, h2, fun A hA => by rw [map_smul, h3 A hA, smul_zero]⟩
    obtain ⟨H, h1, h2, h3⟩ := this
    obtain ⟨A, -, a2, a3, -⟩ := exists_op ρ H
    rw [← a3 x hfix]
    exact h3 A a2
  have hex : ∀ m : M, ∃ p : M, (∀ k, ρ k p = p) ∧ m - p ∈ N := by
    intro m
    obtain ⟨H, h1, h2, h3⟩ := exists_sub ρ hs m
    obtain ⟨A, a1, -, -, a4⟩ := exists_op ρ H
    exact ⟨A m, a1 m h3, a4 m⟩
  choose f hf1 hf2 using hex
  have huniq : ∀ m p : M, (∀ k, ρ k p = p) → m - p ∈ N → f m = p := by
    intro m p hp hm
    rw [← sub_eq_zero]
    refine hdis _ ?_ fun k => by rw [map_sub, hf1, hp]
    have := N.sub_mem hm (hf2 m)
    rwa [sub_sub_sub_cancel_left] at this
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf1, ?_, ?_⟩
  · intro x y
    refine huniq _ _ (fun k => by rw [map_add, hf1, hf1]) ?_
    rw [add_sub_add_comm]
    exact N.add_mem (hf2 x) (hf2 y)
  · intro c x
    refine huniq _ _ (fun k => by rw [map_smul, hf1]) ?_
    rw [RingHom.id_apply, ← smul_sub]
    exact N.smul_mem c (hf2 x)
  · intro m hm
    exact huniq m m hm (by rw [sub_self]; exact N.zero_mem)
  · intro T hT m
    refine (huniq (T m) (T (f m)) (fun k => by rw [← hT, hf1]) ?_).symm
    rw [← map_sub]
    have hle : N ≤ N.comap T := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨k, y, rfl⟩
      exact Submodule.subset_span ⟨k, T y, by rw [map_sub, hT]⟩
    exact hle (hf2 m)

end UpperTheory.Reformulated.B.ExistsAverage
