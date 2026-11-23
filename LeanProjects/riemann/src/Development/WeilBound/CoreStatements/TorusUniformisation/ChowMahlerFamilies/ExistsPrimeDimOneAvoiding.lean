import Mathlib

namespace PositivityTheory.Xgn.PrimeOfDimensionOne

open IsLocalRing

theorem dim_eq_one (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    (f : B) (hf : f ≠ 0) (hm : f ∈ maximalIdeal B)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q ≠ ⊥ → f ∈ Q) : ringKrullDim B = 1 := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.span {f})
  have hcover : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ P ∈ (↑hfin.toFinset : Set (Ideal B)), (id P : Set B) := by
    intro g hg
    simp only [Set.mem_iUnion, Set.Finite.coe_toFinset, id, SetLike.mem_coe, exists_prop]
    have hne : Ideal.span {g} ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal g).1 hg)
    obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes hne
    have hQp := hQ.1.1
    have hgQ : g ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self g)
    by_cases hg0 : g = 0
    · obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes
        (Ideal.span_singleton_ne_top ((mem_maximalIdeal f).1 hm))
      exact ⟨P, hP, hg0 ▸ P.zero_mem⟩
    have hQ0 : Q ≠ ⊥ := fun hb => hg0 (by rw [hb] at hgQ; exact (Submodule.mem_bot B).1 hgQ)
    have hfQ : Ideal.span {f} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).2 (h Q hQp hQ0)
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hfQ
    have hPp := hP.1.1
    have hP0 : P ≠ ⊥ := fun hb => hf (by
      have := hP.1.2 (Ideal.mem_span_singleton_self f)
      rw [hb] at this
      exact (Submodule.mem_bot B).1 this)
    have hQ1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {g}) Q hQ
    have hPeq : P = Q := by
      by_contra hne'
      have hlt := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPQ hne')
      have h1 : 1 ≤ P.height := Order.one_le_iff_ne_zero.2 (fun h0 => hP0 (Ideal.height_eq_zero_iff_eq_bot.1 h0))
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := (by gcongr : (1 : ℕ∞) + 1 ≤ P.height + 1).trans (hlt.trans hQ1)
      norm_num at h2
    exact ⟨P, hP, hPeq ▸ hgQ⟩
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun P hP _ _ =>
    ((Set.Finite.mem_toFinset hfin).1 hP).1.1)).1 hcover
  have hPmem := (Set.Finite.mem_toFinset hfin).1 hP
  have hPp := hPmem.1.1
  have hPm : P = maximalIdeal B := le_antisymm (le_maximalIdeal hPp.ne_top) hmP
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) P hPmem
  have hge : 1 ≤ (maximalIdeal B).height := Order.one_le_iff_ne_zero.2 (fun h0 =>
    hf ((Submodule.mem_bot B).1 (Ideal.height_eq_zero_iff_eq_bot.1 h0 ▸ hm)))
  rw [le_antisymm (hPm ▸ hle) hge]
  rfl

theorem of_mem (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ≠ 0) (hm : f ∈ maximalIdeal A) :
    ∃ P : Ideal A, P.IsPrime ∧ f ∉ P ∧ ringKrullDim (A ⧸ P) = 1 := by
  obtain ⟨P, ⟨hPp, hfP⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 inferInstance
    {P : Ideal A | P.IsPrime ∧ f ∉ P}
    ⟨⊥, Ideal.isPrime_bot, fun h => hf ((Submodule.mem_bot A).1 h)⟩
  refine ⟨P, hPp, hfP, ?_⟩
  have := hPp
  have : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  refine dim_eq_one (A ⧸ P) (Ideal.Quotient.mk P f)
    (fun h0 => hfP (Ideal.Quotient.eq_zero_iff_mem.1 h0)) ?_ ?_
  · refine (mem_maximalIdeal _).2 fun hu => ?_
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ P)ˣ).val
    have h1 : Ideal.Quotient.mk P (f * y - 1) = 0 := by
      rw [map_sub, map_mul, hy, map_one, sub_eq_zero]
      exact hu.mul_val_inv
    have h2 : f * y - 1 ∈ maximalIdeal A :=
      le_maximalIdeal hPp.ne_top (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have h3 : (1 : A) ∈ maximalIdeal A := by
      simpa using sub_mem ((maximalIdeal A).mul_mem_right y hm) h2
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · intro Q hQ hQ0
    by_contra hfQ
    refine hmax (Q.comap (Ideal.Quotient.mk P)) ⟨Ideal.comap_isPrime _ _, hfQ⟩
      (lt_of_le_of_ne (fun a ha => ?_) fun hPQ => hQ0 ?_)
    · show Ideal.Quotient.mk P a ∈ Q
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact Q.zero_mem
    · rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, ← hPQ,
        Ideal.map_quotient_self]

end PositivityTheory.Xgn.PrimeOfDimensionOne

theorem PositivityTheory.Xgn.exists_prime_dim_one_avoiding : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (f : A), f ≠ 0 → ¬ IsField A → ∃ P : Ideal A, P.IsPrime ∧ f ∉ P ∧ ringKrullDim (A ⧸ P) = 1 := by
  intro A _ _ _ _ f hf hA
  have hm : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    fun h => hA (IsLocalRing.isField_iff_maximalIdeal_eq.2 h)
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨P, hP, hfgP, hdim⟩ := PositivityTheory.Xgn.PrimeOfDimensionOne.of_mem A (f * g) (mul_ne_zero hf hg0)
    ((IsLocalRing.maximalIdeal A).mul_mem_left f hg)
  exact ⟨P, hP, fun hfP => hfgP (P.mul_mem_right g hfP), hdim⟩
