import Mathlib

theorem UpperTheory.Reformulated.B.Qe18.hc_avg :
    ∀ {k D M : Type} [inst : Field k] [inst_1 : Group D]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module k M] (ρ : Representation k D M) (N : Subgroup D),
    (↑N.index : k) ≠ (0 : k) →
      ∀ (z : D → M),
        (∀ (g h : D), z (g * h) = z g + ((ρ : D → M →ₗ[k] M) g : M → M) (z h)) →
          (∀ s ∈ N, z s = (0 : M)) → ∃ (m : M), ∀ (g : D), z g = ((ρ : D → M →ₗ[k] M) g : M → M) m - m := by
  intro k D M _ _ _ _ ρ N hN z hz h0
  have hidx : N.index ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  haveI : Fintype (D ⧸ N) := Subgroup.fintypeOfIndexNeZero hidx
  have hcos : ∀ a b : D, (a : D ⧸ N) = (b : D ⧸ N) → z a = z b := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ N := QuotientGroup.eq.mp hab
    have h1 := hz a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h0 _ hmem, map_zero, add_zero] at h1
    exact h1.symm
  have hcard : Fintype.card (D ⧸ N) = N.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have key : ∀ g : D, ∑ q : D ⧸ N, z q.out
      = (N.index : k) • z g + ρ g (∑ q : D ⧸ N, z q.out) := by
    intro g
    have h1 : ∑ q : D ⧸ N, z (g • q).out = ∑ q : D ⧸ N, z q.out :=
      Equiv.sum_comp (MulAction.toPerm g) (fun q : D ⧸ N => z q.out)
    have h2 : ∀ q : D ⧸ N, z (g • q).out = z g + ρ g (z q.out) := by
      intro q
      rw [← hz]
      apply hcos
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.coe_smul_out]
    calc ∑ q : D ⧸ N, z q.out = ∑ q : D ⧸ N, z (g • q).out := h1.symm
      _ = ∑ q : D ⧸ N, (z g + ρ g (z q.out)) := Finset.sum_congr rfl fun q _ => h2 q
      _ = (N.index : k) • z g + ρ g (∑ q : D ⧸ N, z q.out) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, map_sum,
          Nat.cast_smul_eq_nsmul]
  refine ⟨-((N.index : k)⁻¹ • ∑ q : D ⧸ N, z q.out), fun g => ?_⟩
  have h3 : (N.index : k) • z g
      = (∑ q : D ⧸ N, z q.out) - ρ g (∑ q : D ⧸ N, z q.out) :=
    eq_sub_of_add_eq (key g).symm
  calc z g = (N.index : k)⁻¹ • ((N.index : k) • z g) := (inv_smul_smul₀ hN _).symm
    _ = _ := by
      rw [h3, smul_sub, map_neg, map_smul]
      abel
