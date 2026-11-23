import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.FormulaStep

noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix Finset

variable {N : ℕ}

theorem eps_ePl (ε : Fin N → Bool) (i : Fin (nPl ε)) : ε (ePl ε i) = true := by
  exact Subtype.prop (p := fun a => ε a = true) _

theorem eps_eMi (ε : Fin N → Bool) (j : Fin (nMi ε)) : ε (eMi ε j) = false := by
  exact Bool.eq_false_iff.2 (Subtype.prop (p := fun a => ¬ ε a = true) _)

theorem ePl_eq (ε : Fin N → Bool) (i : Fin (nPl ε)) : ePl ε i = (sPlus ε).orderEmbOfFin rfl i := rfl

theorem eMi_eq (ε : Fin N → Bool) (j : Fin (nMi ε)) : eMi ε j = (sMinus ε).orderEmbOfFin rfl j := rfl

theorem ePl_lt_iff (ε : Fin N → Bool) (i j : Fin (nPl ε)) : ePl ε i < ePl ε j ↔ i < j := by
  rw [ePl_eq, ePl_eq]
  exact ((sPlus ε).orderEmbOfFin rfl).lt_iff_lt

theorem eMi_lt_iff (ε : Fin N → Bool) (i j : Fin (nMi ε)) : eMi ε i < eMi ε j ↔ i < j := by
  rw [eMi_eq, eMi_eq]
  exact ((sMinus ε).orderEmbOfFin rfl).lt_iff_lt

theorem ePl_inj (ε : Fin N → Bool) (i j : Fin (nPl ε)) : ePl ε i = ePl ε j ↔ i = j := by
  show blk ε (Sum.inl i) = blk ε (Sum.inl j) ↔ i = j
  rw [(blk ε).injective.eq_iff, Sum.inl.injEq]

theorem eMi_inj (ε : Fin N → Bool) (i j : Fin (nMi ε)) : eMi ε i = eMi ε j ↔ i = j := by
  show blk ε (Sum.inr i) = blk ε (Sum.inr j) ↔ i = j
  rw [(blk ε).injective.eq_iff, Sum.inr.injEq]

theorem ePl_ne_eMi (ε : Fin N → Bool) (i : Fin (nPl ε)) (j : Fin (nMi ε)) : ePl ε i ≠ eMi ε j := by
  intro h
  exact Sum.inl_ne_inr ((blk ε).injective h)

@[to_additive]
theorem prod_split {M : Type*} [CommMonoid M] (ε : Fin N → Bool) (f : Fin N → M) :
    ∏ a, f a = (∏ i, f (ePl ε i)) * ∏ j, f (eMi ε j) := by
  rw [← Equiv.prod_comp (blk ε), Fintype.prod_sum_type]
  rfl

theorem eMi_ne_ePl (ε : Fin N → Bool) (j : Fin (nMi ε)) (i : Fin (nPl ε)) : eMi ε j ≠ ePl ε i := by
  exact fun h => ePl_ne_eMi ε i j h.symm

private theorem exists_ePl_eq_of_true (ε : Fin N → Bool) (b : Fin N) (hb : ε b = true) :
    ∃ k, ePl ε k = b := by
  obtain ⟨x, rfl⟩ := (blk ε).surjective b
  rcases x with k | j
  · exact ⟨k, rfl⟩
  · have h2 : ε (blk ε (Sum.inr j)) = false := eps_eMi ε j
    rw [h2] at hb
    exact absurd hb (by decide)

private theorem exists_eMi_eq_of_false (ε : Fin N → Bool) (b : Fin N) (hb : ε b = false) :
    ∃ k, eMi ε k = b := by
  obtain ⟨x, rfl⟩ := (blk ε).surjective b
  rcases x with k | j
  · have h2 : ε (blk ε (Sum.inl k)) = true := eps_ePl ε k
    rw [h2] at hb
    exact absurd hb (by decide)
  · exact ⟨j, rfl⟩

theorem card_gt_ePl (ε : Fin N → Bool) (i : Fin (nPl ε)) :
    (univ.filter fun b => ePl ε i < b ∧ ε b = ε (ePl ε i)).card = nPl ε - 1 - (i : ℕ) := by
  have hs : (univ.filter fun b => ePl ε i < b ∧ ε b = ε (ePl ε i)) =
      (Finset.Ioi i).map ⟨ePl ε, show Function.Injective (ePl ε) from fun a b h => (ePl_inj ε a b).1 h⟩ := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_Ioi, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hb, he⟩
      rw [eps_ePl ε i] at he
      obtain ⟨k, rfl⟩ := exists_ePl_eq_of_true ε b he
      exact ⟨k, (ePl_lt_iff ε i k).1 hb, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(ePl_lt_iff ε i k).2 hk, by rw [eps_ePl ε i, eps_ePl ε k]⟩
  rw [hs, Finset.card_map, Fin.card_Ioi]

theorem card_lt_ePl (ε : Fin N → Bool) (i : Fin (nPl ε)) :
    (univ.filter fun b => b < ePl ε i ∧ ε b = ε (ePl ε i)).card = (i : ℕ) := by
  have hs : (univ.filter fun b => b < ePl ε i ∧ ε b = ε (ePl ε i)) =
      (Finset.Iio i).map ⟨ePl ε, show Function.Injective (ePl ε) from fun a b h => (ePl_inj ε a b).1 h⟩ := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_Iio, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hb, he⟩
      rw [eps_ePl ε i] at he
      obtain ⟨k, rfl⟩ := exists_ePl_eq_of_true ε b he
      exact ⟨k, (ePl_lt_iff ε k i).1 hb, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(ePl_lt_iff ε k i).2 hk, by rw [eps_ePl ε i, eps_ePl ε k]⟩
  rw [hs, Finset.card_map, Fin.card_Iio]

theorem card_gt_eMi (ε : Fin N → Bool) (i : Fin (nMi ε)) :
    (univ.filter fun b => eMi ε i < b ∧ ε b = ε (eMi ε i)).card = nMi ε - 1 - (i : ℕ) := by
  have hs : (univ.filter fun b => eMi ε i < b ∧ ε b = ε (eMi ε i)) =
      (Finset.Ioi i).map ⟨eMi ε, show Function.Injective (eMi ε) from fun a b h => (eMi_inj ε a b).1 h⟩ := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_Ioi, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hb, he⟩
      rw [eps_eMi ε i] at he
      obtain ⟨k, rfl⟩ := exists_eMi_eq_of_false ε b he
      exact ⟨k, (eMi_lt_iff ε i k).1 hb, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(eMi_lt_iff ε i k).2 hk, by rw [eps_eMi ε i, eps_eMi ε k]⟩
  rw [hs, Finset.card_map, Fin.card_Ioi]

theorem card_lt_eMi (ε : Fin N → Bool) (i : Fin (nMi ε)) :
    (univ.filter fun b => b < eMi ε i ∧ ε b = ε (eMi ε i)).card = (i : ℕ) := by
  have hs : (univ.filter fun b => b < eMi ε i ∧ ε b = ε (eMi ε i)) =
      (Finset.Iio i).map ⟨eMi ε, show Function.Injective (eMi ε) from fun a b h => (eMi_inj ε a b).1 h⟩ := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_Iio, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hb, he⟩
      rw [eps_eMi ε i] at he
      obtain ⟨k, rfl⟩ := exists_eMi_eq_of_false ε b he
      exact ⟨k, (eMi_lt_iff ε k i).1 hb, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(eMi_lt_iff ε k i).2 hk, by rw [eps_eMi ε i, eps_eMi ε k]⟩
  rw [hs, Finset.card_map, Fin.card_Iio]

theorem rhoC_ePl (ε : Fin N → Bool) (i : Fin (nPl ε)) :
    rhoC ε (ePl ε i) = ((nPl ε : ℝ) - 1 - 2 * (i : ℕ)) / 2 := by
  simp only [rhoC]
  rw [card_gt_ePl, card_lt_ePl]
  have hi := i.isLt
  have h1 : (i : ℕ) ≤ nPl ε - 1 := by omega
  have h2 : 1 ≤ nPl ε := by omega
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  push_cast
  ring

theorem rhoC_eMi (ε : Fin N → Bool) (i : Fin (nMi ε)) :
    rhoC ε (eMi ε i) = ((nMi ε : ℝ) - 1 - 2 * (i : ℕ)) / 2 := by
  simp only [rhoC]
  rw [card_gt_eMi, card_lt_eMi]
  have hi := i.isLt
  have h1 : (i : ℕ) ≤ nMi ε - 1 := by omega
  have h2 : 1 ≤ nMi ε := by omega
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  push_cast
  ring

theorem prod_pairs_split {M : Type*} [CommMonoid M] (ε : Fin N → Bool) (g : Fin N → Fin N → M) :
    ∏ a : Fin N, ∏ b ∈ univ.filter (fun b => a < b ∧ ε a = ε b), g a b =
      (∏ i, ∏ j ∈ univ.filter (fun j => i < j), g (ePl ε i) (ePl ε j)) *
        ∏ i, ∏ j ∈ univ.filter (fun j => i < j), g (eMi ε i) (eMi ε j) := by
  rw [prod_split ε]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hs : (univ.filter fun b => ePl ε i < b ∧ ε (ePl ε i) = ε b) =
        (univ.filter fun j => i < j).map ⟨ePl ε, show Function.Injective (ePl ε) from fun a b h => (ePl_inj ε a b).1 h⟩ := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hb, he⟩
        rw [eps_ePl ε i] at he
        obtain ⟨k, rfl⟩ := exists_ePl_eq_of_true ε b he.symm
        exact ⟨k, (ePl_lt_iff ε i k).1 hb, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨(ePl_lt_iff ε i k).2 hk, by rw [eps_ePl ε i, eps_ePl ε k]⟩
    rw [hs, Finset.prod_map]
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hs : (univ.filter fun b => eMi ε i < b ∧ ε (eMi ε i) = ε b) =
        (univ.filter fun j => i < j).map ⟨eMi ε, show Function.Injective (eMi ε) from fun a b h => (eMi_inj ε a b).1 h⟩ := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hb, he⟩
        rw [eps_eMi ε i] at he
        obtain ⟨k, rfl⟩ := exists_eMi_eq_of_false ε b he.symm
        exact ⟨k, (eMi_lt_iff ε i k).1 hb, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨(eMi_lt_iff ε i k).2 hk, by rw [eps_eMi ε i, eps_eMi ε k]⟩
    rw [hs, Finset.prod_map]
    rfl

theorem weyl_formula_compact : FormulaStep := by
  intro N ε Λ
  have hsp := prod_pairs_split ε (fun a b => (Λ + rhoC ε) a - (Λ + rhoC ε) b)
  rw [hsp, wu, wu, mul_div_mul_comm]
  congr 2
  · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, rhoC_ePl]
    ring
  · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, rhoC_eMi]
    ring

theorem dominant_restriction_holds : CDomRes := by
  intro N ε μ Λ hCD
  obtain ⟨c, hc, hsum⟩ := hCD
  constructor
  · refine ⟨fun i j => c (ePl ε i) (ePl ε j),
      fun i j h => ⟨(ePl_lt_iff ε i j).1 (hc _ _ h).1, rfl⟩, ?_⟩
    funext k
    have hk := congr_fun hsum (ePl ε k)
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    have hT0 : ∀ j b, (c (eMi ε j) b : ℝ) * root (eMi ε j) b (ePl ε k) = 0 := by
      intro j b
      by_cases h0 : c (eMi ε j) b = 0
      · simp [h0]
      · have he := (hc _ _ h0).2
        rw [eps_eMi ε j] at he
        have hb : b ≠ ePl ε k := by
          rintro rfl
          rw [eps_ePl ε k] at he
          exact absurd he (by decide)
        have ha : ePl ε k ≠ eMi ε j := ePl_ne_eMi ε k j
        simp [root, Pi.single_apply, ha, hb.symm]
    have hT1 : ∀ i j, (c (ePl ε i) (eMi ε j) : ℝ) = 0 := by
      intro i j
      by_contra h0
      have he := (hc _ _ (by exact_mod_cast h0)).2
      rw [eps_ePl ε i, eps_eMi ε j] at he
      exact absurd he (by decide)
    rw [hk, sum_split ε]
    simp only [hT0, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_split ε]
    simp only [hT1, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [root, Pi.single_apply, ePl_inj]
  · refine ⟨fun i j => c (eMi ε i) (eMi ε j),
      fun i j h => ⟨(eMi_lt_iff ε i j).1 (hc _ _ h).1, rfl⟩, ?_⟩
    funext k
    have hk := congr_fun hsum (eMi ε k)
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    have hT0 : ∀ j b, (c (ePl ε j) b : ℝ) * root (ePl ε j) b (eMi ε k) = 0 := by
      intro j b
      by_cases h0 : c (ePl ε j) b = 0
      · simp [h0]
      · have he := (hc _ _ h0).2
        rw [eps_ePl ε j] at he
        have hb : b ≠ eMi ε k := by
          rintro rfl
          rw [eps_eMi ε k] at he
          exact absurd he (by decide)
        have ha : eMi ε k ≠ ePl ε j := eMi_ne_ePl ε k j
        simp [root, Pi.single_apply, ha, hb.symm]
    have hT1 : ∀ i j, (c (eMi ε i) (ePl ε j) : ℝ) = 0 := by
      intro i j
      by_contra h0
      have he := (hc _ _ (by exact_mod_cast h0)).2
      rw [eps_eMi ε i, eps_ePl ε j] at he
      exact absurd he (by decide)
    rw [hk, sum_split ε]
    simp only [hT0, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_split ε]
    simp only [hT1, zero_mul, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [root, Pi.single_apply, eMi_inj]

end PI.WeylForKWork
