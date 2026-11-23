import Mathlib
import Formalism.PeriodIntegrals.UpqRep

namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC

open Finset

theorem prod_one_add_inv_le (D : Finset ℕ) (h0 : 0 ∉ D) : ∏ d ∈ D, (1 + 1 / (d : ℝ)) ≤ D.card + 1 := by
  induction D using Finset.induction_on_max with
  | empty => simp
  | insert m D hlt ih =>
    have hm : m ∉ D := fun h => lt_irrefl _ (hlt m h)
    have h0' : 0 ∉ D := fun h => h0 (mem_insert_of_mem h)
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun e => h0 (e ▸ mem_insert_self m D)
    have hcard : D.card + 1 ≤ m := by
      have hsub : D ⊆ (range m).erase 0 := fun x hx =>
        mem_erase.2 ⟨fun e => h0' (e ▸ hx), mem_range.2 (hlt x hx)⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (mem_range.2 hm0), card_range] at this
      omega
    rw [prod_insert hm, card_insert_of_notMem hm]
    have ih' := ih h0'
    have hP : 0 ≤ ∏ d ∈ D, (1 + 1 / (d : ℝ)) := prod_nonneg fun d _ => by positivity
    have hc : ((D.card : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hcard
    have hc0 : (0 : ℝ) < (D.card : ℝ) + 1 := by positivity
    have h1 : 1 + 1 / (m : ℝ) ≤ 1 + 1 / ((D.card : ℝ) + 1) := by
      have := one_div_le_one_div_of_le hc0 hc
      linarith
    calc (1 + 1 / (m : ℝ)) * ∏ d ∈ D, (1 + 1 / (d : ℝ))
        ≤ (1 + 1 / ((D.card : ℝ) + 1)) * ((D.card : ℝ) + 1) :=
          mul_le_mul h1 ih' hP (by positivity)
      _ = ((D.card + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          field_simp

variable {n : ℕ}

theorem prod_ratio_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (s : Fin n) (T : Finset (Fin n)) (hs : s ∉ T) :
    ∏ t ∈ T, |x s + 1 - x t| / |x s - x t| ≤ n := by
  classical
  have hne : ∀ t ∈ T, x s ≠ x t := fun t ht e => hs (hinj e ▸ ht)
  rw [← prod_filter_mul_prod_filter_not T (fun t => x t < x s)]

  have hlow : ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t| ≤ 1 := by
    apply prod_le_one (fun t _ => by positivity)
    intro t ht
    obtain ⟨ht, hlt⟩ := mem_filter.1 ht
    have hgt : x s < x t := lt_of_le_of_ne (not_lt.1 hlt) (hne t ht)
    obtain ⟨m, hmv⟩ := hint t s
    have hm1 : (1 : ℝ) ≤ x t - x s := by
      rw [hmv]
      have : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hgt)
      exact_mod_cast this
    rw [div_le_one (abs_pos.2 (sub_ne_zero.2 (hne t ht)))]
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith

  set Tp := T.filter (fun t => x t < x s) with hTp
  let dN : Fin n → ℕ := fun t => (⌊x s - x t⌋).toNat
  have hdN : ∀ t ∈ Tp, ((dN t : ℕ) : ℝ) = x s - x t ∧ 1 ≤ x s - x t := by
    intro t ht
    obtain ⟨-, hlt⟩ := mem_filter.1 ht
    obtain ⟨m, hmv⟩ := hint s t
    have hm0 : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hlt)
    refine ⟨?_, ?_⟩
    · simp only [dN, hmv, Int.floor_intCast]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0.le]
    · rw [hmv]; exact_mod_cast hm0
  have hinjOn : Set.InjOn dN Tp := by
    intro t ht t' ht' e
    have h1 := (hdN t ht).1
    have h2 := (hdN t' ht').1
    apply hinj
    have : x s - x t = x s - x t' := by rw [← h1, ← h2, e]
    linarith
  have hup : ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| = ∏ d ∈ Tp.image dN, (1 + 1 / (d : ℝ)) := by
    rw [prod_image hinjOn]
    refine prod_congr rfl fun t ht => ?_
    obtain ⟨h1, h2⟩ := hdN t ht
    rw [h1, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    field_simp
    ring
  have hD0 : 0 ∉ Tp.image dN := by
    intro h
    obtain ⟨t, ht, e⟩ := mem_image.1 h
    have h1 := hdN t ht
    rw [e] at h1
    simp at h1
    linarith [h1.1, h1.2]
  have hbound := prod_one_add_inv_le (Tp.image dN) hD0
  rw [card_image_of_injOn hinjOn] at hbound
  have hTcard : Tp.card + 1 ≤ n := by
    have h1 : Tp.card ≤ T.card := card_le_card (filter_subset _ _)
    have h2 : T.card < n := by
      have := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ T, fun e => hs (e ▸ mem_univ s)⟩)
      simpa using this
    omega
  have hupnn : 0 ≤ ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| := prod_nonneg fun t _ => by positivity
  calc (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) *
        ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t|
      ≤ (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) * 1 := mul_le_mul_of_nonneg_left hlow hupnn
    _ ≤ (n : ℝ) := by
        rw [mul_one, hup]
        refine hbound.trans ?_
        exact_mod_cast hTcard

def numHC (x : Fin n → ℝ) : ℝ := ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |x a - x b|

theorem sq_prod_lt (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a) :
    (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, g a b := by
  have h1 : ∀ a : Fin n, ∏ b ∈ univ.erase a, g a b =
      (∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) * ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b := by
    intro a
    rw [← prod_union]
    · congr 1
      ext b
      simp only [mem_erase, mem_univ, and_true, mem_union, mem_filter, true_and]
      constructor
      · intro h; rcases lt_or_gt_of_ne h with h | h <;> [exact Or.inr h; exact Or.inl h]
      · rintro (h | h) <;> [exact ne_of_gt h; exact ne_of_lt h]
    · rw [disjoint_filter]
      intro b _ h1 h2
      exact lt_asymm h1 h2
  rw [prod_congr rfl (fun a _ => h1 a), prod_mul_distrib, sq]
  congr 1
  have hB : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b =
      ∏ b : Fin n, ∏ a ∈ univ.filter (fun a : Fin n => b < a), g a b :=
    prod_comm' (by intro a b; simp)
  rw [hB]
  exact prod_congr rfl fun b _ => prod_congr rfl fun a _ => hg b a

theorem numHC_addI_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    numHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * numHC x := by
  classical
  set y : Fin n → ℝ := fun i => x i + if i ∈ I then 1 else 0 with hydef
  set f : Fin n → Fin n → ℝ := fun a b => |y a - y b| / |x a - x b| with hf
  have hx0 : ∀ a b, a ≠ b → |x a - x b| ≠ 0 := fun a b h =>
    abs_ne_zero.2 (sub_ne_zero.2 fun e => h (hinj e))
  have hfs : ∀ a b, f a b = f b a := fun a b => by simp only [hf, abs_sub_comm]
  have hy : ∀ a b, a ≠ b → |y a - y b| = f a b * |x a - x b| := fun a b h => by
    simp only [hf]; rw [div_mul_cancel₀ _ (hx0 a b h)]
  have hf1 : ∀ a b, a ≠ b → (a ∈ I ↔ b ∈ I) → f a b = 1 := by
    intro a b h hab
    simp only [hf, hydef]
    have : (x a + if a ∈ I then 1 else 0) - (x b + if b ∈ I then 1 else 0) = x a - x b := by
      by_cases ha : a ∈ I
      · rw [if_pos ha, if_pos (hab.1 ha)]; ring
      · rw [if_neg ha, if_neg (fun hb => ha (hab.2 hb))]; ring
    rw [this, div_self (hx0 a b h)]
  have hsqy : numHC y ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b| :=
    sq_prod_lt _ fun a b => abs_sub_comm _ _
  have hsqx : numHC x ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |x a - x b| :=
    sq_prod_lt _ fun a b => abs_sub_comm _ _
  have hsplit : ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b| =
      (∏ a : Fin n, ∏ b ∈ univ.erase a, f a b) * numHC x ^ 2 := by
    rw [hsqx, ← prod_mul_distrib]
    refine prod_congr rfl fun a _ => ?_
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => hy a b (ne_of_mem_erase hb).symm
  set Pr := ∏ s ∈ I, ∏ t ∈ univ \ I, f s t with hPr
  have hff : ∏ a : Fin n, ∏ b ∈ univ.erase a, f a b = Pr ^ 2 := by
    have hin : ∀ a ∈ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ univ \ I, f a b := by
      intro a ha
      symm
      apply prod_subset
      · intro b hb
        rw [mem_sdiff] at hb
        exact mem_erase.2 ⟨fun e => hb.2 (e ▸ ha), mem_univ b⟩
      · intro b hb hb'
        have hba : b ≠ a := ne_of_mem_erase hb
        have hbI : b ∈ I := by
          by_contra h
          exact hb' (mem_sdiff.2 ⟨mem_univ b, h⟩)
        exact hf1 a b hba.symm ⟨fun _ => hbI, fun _ => ha⟩
    have hout : ∀ a ∉ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ I, f a b := by
      intro a ha
      symm
      apply prod_subset
      · intro b hb
        exact mem_erase.2 ⟨fun e => ha (e ▸ hb), mem_univ b⟩
      · intro b hb hb'
        have hba : b ≠ a := ne_of_mem_erase hb
        exact hf1 a b hba.symm ⟨fun h => absurd h ha, fun h => absurd h hb'⟩
    rw [← prod_filter_mul_prod_filter_not univ (fun a => a ∈ I)]
    have e1 : univ.filter (fun a : Fin n => a ∈ I) = I := by ext a; simp
    have e2 : univ.filter (fun a : Fin n => a ∉ I) = univ \ I := by ext a; simp
    rw [e1, e2, prod_congr rfl hin, prod_congr rfl (fun a ha => hout a (mem_sdiff.1 ha).2)]
    have hC : ∏ a ∈ univ \ I, ∏ b ∈ I, f a b = ∏ b ∈ I, ∏ a ∈ univ \ I, f a b := prod_comm
    rw [hC, sq]
    congr 1
    exact prod_congr rfl fun s _ => prod_congr rfl fun t _ => hfs t s
  have hP0 : 0 ≤ Pr := prod_nonneg fun s _ => prod_nonneg fun t _ => by positivity
  have hPn : Pr ≤ (n : ℝ) ^ I.card := by
    rw [← prod_const]
    refine prod_le_prod (fun s _ => prod_nonneg fun t _ => by positivity) fun s hs => ?_
    have e : ∏ t ∈ univ \ I, f s t = ∏ t ∈ univ \ I, |x s + 1 - x t| / |x s - x t| := by
      refine prod_congr rfl fun t ht => ?_
      have htI : t ∉ I := (mem_sdiff.1 ht).2
      simp only [hf, hydef, if_pos hs, if_neg htI]
      congr 1
      ring_nf
    rw [e]
    exact prod_ratio_le x hinj hint s (univ \ I) (fun h => (mem_sdiff.1 h).2 hs)
  have hny : 0 ≤ numHC y := prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _
  have hnx : 0 ≤ numHC x := prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _
  have hsq : numHC y ^ 2 ≤ ((n : ℝ) ^ I.card * numHC x) ^ 2 := by
    rw [hsqy, hsplit, hff, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP0 hPn 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ hny (by positivity) two_ne_zero).1 hsq

theorem fdegHC_addI_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    PI.UpqRep.fdegHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * PI.UpqRep.fdegHC x := by
  unfold PI.UpqRep.fdegHC
  have hD : 0 ≤ ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) :=
    prod_nonneg fun a _ => prod_nonneg fun b hb => by
      have := (mem_filter.1 hb).2
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
      linarith
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (numHC_addI_le x hinj hint I) hD

end Formalism.FourierDecayAlt.P.CutBP.JmuHC
