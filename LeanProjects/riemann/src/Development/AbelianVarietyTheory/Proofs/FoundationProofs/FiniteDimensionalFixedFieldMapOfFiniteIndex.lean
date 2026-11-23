import Mathlib

open Polynomial IntermediateField

namespace GlobalTheory

theorem isSeparable_and_natDegree_le_of_fixed {F E : Type} [Field F] [Field E] [Algebra F E]
    (G : Type) [Group G] (act : G →* (E ≃ₐ[F] E)) (N : Subgroup G) [N.FiniteIndex]
    (hG : ∀ x : E, (∀ g, act g x = x) → x ∈ (⊥ : IntermediateField F E))
    (x : E) (hx : ∀ n ∈ N, act n x = x) :
    IsIntegral F x ∧ IsSeparable F x ∧ (minpoly F x).natDegree ≤ N.index := by
  classical
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let f : G ⧸ N → E := fun q => Quotient.liftOn' q (fun g => act g x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have := hx _ hab
    show act a x = act b x
    calc act a x = act a (act (a⁻¹ * b) x) := by rw [this]
      _ = act b x := by rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left])
  have hf : ∀ g : G, f (QuotientGroup.mk g) = act g x := fun g => rfl
  let S : Finset E := Finset.univ.image f
  have hS : ∀ y, y ∈ S ↔ ∃ g : G, act g x = y := by
    intro y
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H g => exact ⟨g, (hf g).symm⟩
    · rintro ⟨g, rfl⟩; exact ⟨_, hf g⟩
  have hcard : S.card ≤ N.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    exact Finset.card_image_le.trans (by simp)
  let p : E[X] := ∏ y ∈ S, (X - C y)
  have hpmon : p.Monic := monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hpsep : p.Separable := separable_prod_X_sub_C_iff'.2 (fun a _ b _ h => h)
  have hpdeg : p.natDegree = S.card := natDegree_finsetProd_X_sub_C_eq_card S id
  have hpinv : ∀ g : G, p.map ((act g : E ≃ₐ[F] E) : E →+* E) = p := by
    intro g
    simp only [p, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
    have himg : S.image (act g) = S := by
      ext y
      simp only [Finset.mem_image, hS]
      constructor
      · rintro ⟨z, ⟨h, rfl⟩, rfl⟩
        exact ⟨g * h, by rw [map_mul, AlgEquiv.mul_apply]⟩
      · rintro ⟨h, rfl⟩
        exact ⟨act (g⁻¹ * h) x, ⟨g⁻¹ * h, rfl⟩, by
          rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]⟩
    conv_rhs => rw [← himg]
    rw [Finset.prod_image (fun a _ b _ h => (act g).injective h)]
    rfl
  have hlift : p ∈ lifts (algebraMap F E) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have : p.coeff n ∈ (⊥ : IntermediateField F E) := by
      apply hG
      intro g
      conv_rhs => rw [← hpinv g]
      rw [coeff_map]
      rfl
    exact mem_bot.1 this
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := lifts_and_natDegree_eq_and_monic hlift hpmon
  have hxS : x ∈ S := (hS x).2 ⟨1, by simp⟩
  have hqx : aeval x q = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hqmap, eval_prod]
    exact Finset.prod_eq_zero hxS (by simp)
  have hint : IsIntegral F x := ⟨q, hqmon, hqx⟩
  have hdvd : minpoly F x ∣ q := minpoly.dvd F x hqx
  have hqsep : q.Separable := (separable_map (algebraMap F E)).1 (hqmap ▸ hpsep)
  refine ⟨hint, hqsep.of_dvd hdvd, ?_⟩
  calc (minpoly F x).natDegree ≤ q.natDegree := natDegree_le_of_dvd hdvd hqmon.ne_zero
    _ = S.card := by rw [hqdeg, hpdeg]
    _ ≤ N.index := hcard

theorem finiteDimensional_fixedField_map_of_finiteIndex : ∀ {F E : Type} [Field F] [Field E]
    [Algebra F E] (G : Type) [Group G] (act : G →* (E ≃ₐ[F] E)) (N : Subgroup G), N.FiniteIndex →
    (∀ x : E, (∀ g, act g x = x) → x ∈ (⊥ : IntermediateField F E)) →
    FiniteDimensional F (IntermediateField.fixedField (N.map act)) := by
  intro F E _ _ _ G _ act N hN hG
  set L := IntermediateField.fixedField (N.map act) with hLdef
  have key : ∀ y ∈ L, IsIntegral F y ∧ IsSeparable F y ∧ (minpoly F y).natDegree ≤ N.index := by
    intro y hy
    refine isSeparable_and_natDegree_le_of_fixed G act N hG y fun n hn => ?_
    exact (mem_fixedField_iff _ _).1 hy _ (Subgroup.mem_map_of_mem act hn)
  have hbound : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ N.index := by
    intro y hy
    rw [adjoin.finrank (key y hy).1]
    exact (key y hy).2.2
  let D : Set ℕ := {d | ∃ y ∈ L, Module.finrank F F⟮y⟯ = d}
  have hDne : D.Nonempty := ⟨_, 0, L.zero_mem, rfl⟩
  have hDbdd : BddAbove D := ⟨N.index, by rintro d ⟨y, hy, rfl⟩; exact hbound y hy⟩
  obtain ⟨x, hxL, hxmax⟩ := Nat.sSup_mem hDne hDbdd
  have hle : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ Module.finrank F F⟮x⟯ := by
    intro y hy
    rw [hxmax]
    exact le_csSup hDbdd ⟨y, hy, rfl⟩
  have hLx : L ≤ F⟮x⟯ := by
    intro y hy
    have hx := key x hxL
    have hy' := key y hy
    haveI := isSeparable_adjoin_pair_of_isSeparable F E hx.2.1 hy'.2.1
    haveI : FiniteDimensional F F⟮x, y⟯ := finiteDimensional_adjoin (by
      rintro z (rfl | rfl)
      · exact hx.1
      · exact hy'.1)
    obtain ⟨α, hα⟩ := Field.exists_primitive_element F F⟮x, y⟯
    have hz : F⟮(α : E)⟯ = F⟮x, y⟯ := by
      simpa only [lift_adjoin_simple, lift_top] using congr_arg lift hα
    have hKL : F⟮x, y⟯ ≤ L := by
      rw [adjoin_le_iff]
      rintro z (rfl | rfl)
      · exact hxL
      · exact hy
    have hxK : F⟮x⟯ ≤ F⟮x, y⟯ := adjoin_simple_le_iff.2 (subset_adjoin F _ (by simp))
    have heq : F⟮x⟯ = F⟮x, y⟯ := by
      apply eq_of_le_of_finrank_le hxK
      rw [← hz]
      exact hle _ (hKL α.2)
    rw [heq]
    exact subset_adjoin F _ (by simp)
  haveI : FiniteDimensional F F⟮x⟯ := adjoin.finiteDimensional (key x hxL).1
  exact Module.Finite.of_injective (IntermediateField.inclusion hLx).toLinearMap
    (IntermediateField.inclusion_injective hLx)

end GlobalTheory
