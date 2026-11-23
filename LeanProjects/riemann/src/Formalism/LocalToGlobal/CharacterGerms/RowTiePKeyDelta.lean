import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

open RowTiePE0

section Val

variable {C : Type} [Field C] {V : VF C}

theorem mm_exists {a : C} (h : V.MM a) : ∃ r : ℝ, 0 < r ∧ V.Ge r a := by
  unfold VF.MM at h
  unfold VF.Ge
  cases hva : V.v a with
  | top => exact ⟨1, one_pos, le_top⟩
  | coe x =>
    rw [hva] at h
    exact ⟨x, by exact_mod_cast h, le_rfl⟩

theorem mm_of_ge {a : C} {r : ℝ} (hr : 0 < r) (h : V.Ge r a) : V.MM a := by
  unfold VF.MM
  unfold VF.Ge at h
  exact lt_of_lt_of_le (by exact_mod_cast hr) h

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at ha hb ⊢
  exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ a b)

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM at ha ⊢
  rw [AddValuation.map_neg]
  exact ha

theorem v_unit {x : C} (hx : V.MM (x - 1)) : V.v x = 0 := by
  unfold VF.MM at hx
  have h1 : V.v (1 : C) = 0 := AddValuation.map_one _
  have e : x = (x - 1) + 1 := by ring
  rw [e, AddValuation.map_add_of_distinct_val _ (by rw [h1]; exact ne_of_gt hx), h1]
  exact min_eq_right hx.le

private lemma le_v_finset_sum_of_forall_le {ι : Type} (S : Finset ι) (f : ι → C) (c : WithTop ℝ)
    (h : ∀ i ∈ S, c ≤ V.v (f i)) : c ≤ V.v (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, AddValuation.map_zero]; exact le_top
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (le_min (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) ?_
    exact AddValuation.map_add _ _ _

private lemma le_v_pow_sub_pow_of_le_v_sub {s t : C} (hs : (0 : WithTop ℝ) ≤ V.v s) (ht : (0 : WithTop ℝ) ≤ V.v t)
    {c : WithTop ℝ} (h : c ≤ V.v (s - t)) (i : ℕ) : c ≤ V.v (s ^ i - t ^ i) := by
  rw [← geom_sum₂_mul, AddValuation.map_mul]
  have h0 : (0 : WithTop ℝ) ≤ V.v (∑ j ∈ Finset.range i, s ^ j * t ^ (i - 1 - j)) := by
    apply le_v_finset_sum_of_forall_le
    intro j _
    rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow]
    exact add_nonneg (nsmul_nonneg hs _) (nsmul_nonneg ht _)
  calc c = 0 + c := (zero_add c).symm
    _ ≤ _ := add_le_add h0 h

theorem pow_l_close {s t : C} (hs : V.Ge 0 s) (ht : V.Ge 0 t) {r : ℝ} (hr : 0 ≤ r) (h : V.Ge r (s - t)) :
    V.Ge (r + min 1 r) (s ^ V.l - t ^ V.l) := by
  unfold VF.Ge at hs ht h ⊢
  have hs0 : (0 : WithTop ℝ) ≤ V.v s := by simpa using hs
  have ht0 : (0 : WithTop ℝ) ≤ V.v t := by simpa using ht
  have e : ∑ i ∈ Finset.range V.l, t ^ i * t ^ (V.l - 1 - i) = (V.l : C) * t ^ (V.l - 1) := by
    have hc : ∀ i ∈ Finset.range V.l, t ^ i * t ^ (V.l - 1 - i) = t ^ (V.l - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have key : ∑ i ∈ Finset.range V.l, s ^ i * t ^ (V.l - 1 - i)
      = (V.l : C) * t ^ (V.l - 1) + ∑ i ∈ Finset.range V.l, (s ^ i - t ^ i) * t ^ (V.l - 1 - i) := by
    rw [← e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hd : V.v (s ^ V.l - t ^ V.l)
      = V.v (s - t) + V.v (∑ i ∈ Finset.range V.l, s ^ i * t ^ (V.l - 1 - i)) := by
    rw [← geom_sum₂_mul, AddValuation.map_mul]
    exact add_comm _ _
  have hA : (1 : WithTop ℝ) ≤ V.v ((V.l : C) * t ^ (V.l - 1)) := by
    rw [AddValuation.map_mul, V.4]
    calc (1 : WithTop ℝ) = 1 + 0 := (add_zero 1).symm
      _ ≤ 1 + V.v (t ^ (V.l - 1)) :=
        add_le_add le_rfl (show (0 : WithTop ℝ) ≤ V.v (t ^ (V.l - 1)) by
          rw [AddValuation.map_pow]; exact nsmul_nonneg ht0 _)
  have hB : (r : WithTop ℝ) ≤ V.v (∑ i ∈ Finset.range V.l, (s ^ i - t ^ i) * t ^ (V.l - 1 - i)) := by
    apply le_v_finset_sum_of_forall_le
    intro i _
    rw [AddValuation.map_mul]
    calc (r : WithTop ℝ) = r + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add (le_v_pow_sub_pow_of_le_v_sub hs0 ht0 h i)
        (show (0 : WithTop ℝ) ≤ V.v (t ^ (V.l - 1 - i)) by
          rw [AddValuation.map_pow]; exact nsmul_nonneg ht0 _)
  have hG : ((min 1 r : ℝ) : WithTop ℝ) ≤ V.v (∑ i ∈ Finset.range V.l, s ^ i * t ^ (V.l - 1 - i)) := by
    rw [key]
    refine le_trans ?_ (AddValuation.map_add _ _ _)
    rw [WithTop.coe_min, WithTop.coe_one]
    exact min_le_min hA hB
  rw [hd, WithTop.coe_add]
  exact add_le_add h hG

private lemma ge_zero_pow_of_ge_zero {s : C} (hs : V.Ge 0 s) (n : ℕ) : V.Ge 0 (s ^ n) := by
  unfold VF.Ge at hs ⊢
  rw [AddValuation.map_pow]
  have h0 : (0 : WithTop ℝ) ≤ V.v s := by simpa using hs
  simpa using nsmul_nonneg h0 n

theorem pow_lk_close {s t : C} (hs : V.Ge 0 s) (ht : V.Ge 0 t) {r : ℝ} (hr : 0 ≤ r) (h : V.Ge r (s - t))
    (k : ℕ) (hk : 0 < k) : V.Ge (r + min 1 r) (s ^ V.l ^ k - t ^ V.l ^ k) := by
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rw [zero_add, pow_one]
      exact pow_l_close hs ht hr h
    · have h1 := ih hk'
      have hR : 0 ≤ r + min 1 r := add_nonneg hr (le_min zero_le_one hr)
      have h2 := pow_l_close (ge_zero_pow_of_ge_zero hs _) (ge_zero_pow_of_ge_zero ht _) hR h1
      rw [pow_succ, pow_mul, pow_mul]
      unfold VF.Ge at h2 ⊢
      refine le_trans ?_ h2
      exact_mod_cast le_add_of_nonneg_right (le_min zero_le_one hR)

end Val

section Main

private lemma mm_pow_l_pow_sub_of_mm_sub {C : Type} [Field C] {V : VF C} {s t : C} (hs : V.Ge 0 s) (ht : V.Ge 0 t)
    (h : V.MM (s - t)) (k : ℕ) : V.MM (s ^ V.l ^ k - t ^ V.l ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, pow_one]
    exact h
  · obtain ⟨r, hr, hge⟩ := mm_exists h
    exact mm_of_ge (add_pos_of_pos_of_nonneg hr (le_min zero_le_one hr.le))
      (pow_lk_close hs ht hr.le hge k hk)

private lemma mm_em_add_sub_em_pow_l_pow {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n d : ℕ} [NeZero d]
    (K : KeyData C V O n d) (a : ZMod d) (y : O) (k : ℕ) :
    V.MM ((K.em (a + k)) y - (K.em a) y ^ V.l ^ k) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, add_zero, pow_zero, pow_one, sub_self]
    unfold VF.MM
    rw [AddValuation.map_zero]
    simp
  | succ k ih =>
    have h1 := K.6 (a + k) y
    have h2 := mm_pow_l_pow_sub_of_mm_sub (K.5 (a + k) y) (ge_zero_pow_of_ge_zero (K.5 a y) _) ih 1
    simp only [pow_one] at h2
    have h3 := mm_add h1 h2
    rw [sub_add_sub_cancel] at h3
    rw [Nat.cast_succ, ← add_assoc, pow_succ, pow_mul]
    exact h3

theorem keyDelta_holds : KeyDeltaSt := by
  intro C _ _ V O _ n d _ K χ c hχ hcong
  have hunit : V.v (χ K.7) = 0 := by
    apply v_unit
    have h := mm_add (hcong K.7) (K.9 c)
    rwa [sub_add_sub_cancel] at h
  have hunit' : V.v ((K.em c) K.7) = 0 := v_unit (K.9 c)
  have hrad : ∀ x : O, (∀ a, V.MM ((K.em a) x)) → ∀ r : ℝ, (∀ w, V.Ge r (χ w - (K.em c) w)) →
      V.Ge (r + 1) (χ x - (K.em c) x) := by
    intro x hx r hr
    obtain ⟨w, hw⟩ := K.10 x hx
    have hχw : χ K.7 * χ x = (V.l : C) * χ w := by rw [← map_mul, hw, map_mul, map_natCast]
    have hew : (K.em c) K.7 * (K.em c) x = (V.l : C) * (K.em c) w := by
      rw [← map_mul, hw, map_mul, map_natCast]
    have hid : χ K.7 * (χ x - (K.em c) x)
        = (V.l : C) * (χ w - (K.em c) w) + -((χ K.7 - (K.em c) K.7) * (K.em c) x) := by
      linear_combination hχw - hew
    have hex : (1 : WithTop ℝ) ≤ V.v ((K.em c) x) := by
      have h := congrArg V.v hew
      rw [AddValuation.map_mul, AddValuation.map_mul, hunit', zero_add, V.4] at h
      rw [h]
      have h0 := K.5 c w
      unfold VF.Ge at h0
      calc (1 : WithTop ℝ) = 1 + 0 := (add_zero 1).symm
        _ ≤ 1 + V.v ((K.em c) w) := add_le_add le_rfl (show (0 : WithTop ℝ) ≤ V.v ((K.em c) w) by simpa using h0)
    have hv : V.v (χ x - (K.em c) x) = V.v (χ K.7 * (χ x - (K.em c) x)) := by
      rw [AddValuation.map_mul, hunit, zero_add]
    unfold VF.Ge
    rw [hv, hid]
    refine le_trans (le_min ?_ ?_) (AddValuation.map_add _ _ _)
    · rw [AddValuation.map_mul, V.4, WithTop.coe_add, WithTop.coe_one, add_comm (1 : WithTop ℝ)]
      exact add_le_add (show (r : WithTop ℝ) ≤ _ from hr w) le_rfl
    · rw [AddValuation.map_neg, AddValuation.map_mul, WithTop.coe_add, WithTop.coe_one]
      exact add_le_add (show (r : WithTop ℝ) ≤ _ from hr K.7) hex
  have hradY : ∀ y : O, ∀ a, V.MM ((K.em a) (y ^ V.l ^ d - y)) := by
    intro y a
    have h := mm_em_add_sub_em_pow_l_pow K a y d
    rw [ZMod.natCast_self, add_zero] at h
    rw [map_sub, map_pow]
    have h' := mm_neg h
    rwa [neg_sub] at h'
  have step : ∀ r : ℝ, (∀ w, V.Ge r (χ w - (K.em c) w)) → ∀ y, V.Ge (r + 1) (χ y - (K.em c) y) := by
    intro r hr y
    have hx := hrad _ (hradY y) r hr
    have hpow : ∀ ρ : ℝ, 0 < ρ → V.Ge ρ (χ y - (K.em c) y) →
        V.Ge (ρ + min 1 ρ) (χ (y ^ V.l ^ d) - (K.em c) (y ^ V.l ^ d)) := by
      intro ρ hρ hge
      rw [map_pow, map_pow]
      exact pow_lk_close (hχ y) (K.5 c y) hρ.le hge d (Nat.pos_of_ne_zero (NeZero.ne d))
    have hdec : χ y - (K.em c) y = (χ (y ^ V.l ^ d) - (K.em c) (y ^ V.l ^ d))
        + -(χ (y ^ V.l ^ d - y) - (K.em c) (y ^ V.l ^ d - y)) := by
      simp only [map_sub]
      ring
    unfold VF.Ge
    cases hv : V.v (χ y - (K.em c) y) with
    | top => exact le_top
    | coe ρ =>
      have hρ : 0 < ρ := by
        have h := hcong y
        unfold VF.MM at h
        rw [hv] at h
        exact_mod_cast h
      have hge : V.Ge ρ (χ y - (K.em c) y) := by
        unfold VF.Ge
        rw [hv]
      have h1 := hpow ρ hρ hge
      unfold VF.Ge at h1 hx
      have h2 : min ((ρ + min 1 ρ : ℝ) : WithTop ℝ) ((r + 1 : ℝ) : WithTop ℝ) ≤ (ρ : WithTop ℝ) := by
        rw [← hv, hdec]
        refine le_trans (min_le_min h1 ?_) (AddValuation.map_add _ _ _)
        rw [AddValuation.map_neg]
        exact hx
      rw [← WithTop.coe_min, WithTop.coe_le_coe] at h2
      rw [WithTop.coe_le_coe]
      rcases le_total (r + 1) (ρ + min 1 ρ) with hle | hle
      · rw [min_eq_right hle] at h2
        exact h2
      · rw [min_eq_left hle] at h2
        have : 0 < min 1 ρ := lt_min one_pos hρ
        linarith
  have all : ∀ N : ℕ, ∀ y, V.Ge N (χ y - (K.em c) y) := by
    intro N
    induction N with
    | zero =>
      intro y
      rw [Nat.cast_zero]
      have h0 := hχ y
      have h1 := K.5 c y
      unfold VF.Ge at h0 h1 ⊢
      rw [sub_eq_add_neg]
      refine le_trans (le_min h0 ?_) (AddValuation.map_add _ _ _)
      rw [AddValuation.map_neg]
      exact h1
    | succ N ih =>
      intro y
      rw [Nat.cast_succ]
      exact step N ih y
  intro y
  have htop : V.v (χ y - (K.em c) y) = ⊤ := by
    cases hv : V.v (χ y - (K.em c) y) with
    | top => rfl
    | coe ρ =>
      exfalso
      obtain ⟨N, hN⟩ := exists_nat_gt ρ
      have h := all N y
      unfold VF.Ge at h
      rw [hv, WithTop.coe_le_coe] at h
      linarith
  rw [AddValuation.top_iff] at htop
  exact sub_eq_zero.mp htop

end Main

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
