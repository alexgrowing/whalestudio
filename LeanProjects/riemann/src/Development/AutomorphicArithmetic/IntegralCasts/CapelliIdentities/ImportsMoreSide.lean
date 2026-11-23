import Mathlib

theorem UpperTheory.Reformulated.B.Qi36.aux :
    ∀ {R Q M : Type} [inst : CommRing R] [inst_1 : Group Q]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (π : Representation R Q M) (H : Subgroup Q) (f : Q → M),
    (∀ (g h : Q), f (g * h) = f g + ((π : Q → M →ₗ[R] M) g : M → M) (f h)) →
      (∀ u ∈ H, f u = (0 : M)) → ∃ (m : M), ∀ (g : Q), H.index • f g = ((π : Q → M →ₗ[R] M) g : M → M) m - m := by
  intro R Q M _ _ _ _ π H f hf hH
  by_cases h0 : H.index = 0
  · exact ⟨0, fun g => by simp [h0]⟩
  haveI : Finite (Q ⧸ H) := Nat.finite_of_card_ne_zero h0
  letI : Fintype (Q ⧸ H) := Fintype.ofFinite _
  have key : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b := by
    intro a b hab
    have hm : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hf a (a⁻¹ * b)
    rw [hH _ hm, map_zero, add_zero, mul_inv_cancel_left] at h1
    exact h1.symm
  have step : ∀ (g : Q) (x : Q ⧸ H), f (g • x).out = f g + π g (f x.out) := by
    intro g x
    rw [← hf]
    apply key
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe, QuotientGroup.out_eq']
  refine ⟨-∑ x : Q ⧸ H, f x.out, fun g => ?_⟩
  have hs : ∑ x : Q ⧸ H, f (g • x).out = ∑ x : Q ⧸ H, f x.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun x : Q ⧸ H => f x.out)
  simp only [step, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs
  rw [← map_sum] at hs
  rw [Subgroup.index, Nat.card_eq_fintype_card, map_neg, sub_neg_eq_add,
    eq_sub_of_add_eq hs]
  abel
