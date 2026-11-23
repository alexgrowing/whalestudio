import Mathlib

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.cardsep :
    ∀ (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (q : ℕ), q ≠ 0 → ∀ S : Set M,
    (∀ a ∈ S, ∀ b ∈ S, ∀ x : M, a - b = q • x → a = b) → S.Finite ∧ S.ncard ≤ q ^ Module.finrank ℤ M := by
  intro M _ _ _ q hq S hS
  haveI : NeZero q := ⟨hq⟩
  set r := Module.finrank ℤ M
  let bs := Module.finBasis ℤ M
  let f : M → (Fin r → ZMod q) := fun m i => ((bs.equivFun m i : ℤ) : ZMod q)
  have hinj : Set.InjOn f S := by
    intro a ha c hc hac
    have hdvd : ∀ i, (q : ℤ) ∣ bs.equivFun (a - c) i := by
      intro i
      have h := congrFun hac i
      simp only [f] at h
      rw [map_sub, Pi.sub_apply]
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h.symm
      simpa using this
    refine hS a ha c hc (bs.equivFun.symm fun i => bs.equivFun (a - c) i / q) ?_
    apply bs.equivFun.injective
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd i)).symm
  have himg : (f '' S).Finite := Set.toFinite _
  have hfin : S.Finite := Set.Finite.of_finite_image himg hinj
  refine ⟨hfin, ?_⟩
  rw [← hinj.ncard_image]
  calc (f '' S).ncard ≤ (Set.univ : Set (Fin r → ZMod q)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    _ = q ^ r := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
