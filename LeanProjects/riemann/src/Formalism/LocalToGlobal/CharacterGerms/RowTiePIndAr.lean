import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTAvg

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace IndAr

variable {C : Type} [Field C] {V : VF C}

def Cg (V : VF C) (δ : ℝ) (x y : C) : Prop := V.Ge δ (x - y)

private theorem ge_add_lemma {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a + b) :=
  le_trans (le_min ha hb) (V.v.map_add a b)

private theorem ge_mul_lemma_2 {w w' : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w' b) : V.Ge (w + w') (a * b) := by
  unfold VF.Ge at *
  rw [AddValuation.map_mul, WithTop.coe_add]
  exact add_le_add ha hb

private theorem ge_mono_lemma_3 {w w' : ℝ} {a : C} (ha : V.Ge w a) (h : w' ≤ w) : V.Ge w' a :=
  le_trans (WithTop.coe_le_coe.2 h) ha

private theorem ge_neg_lemma_4 {w : ℝ} {a : C} (ha : V.Ge w a) : V.Ge w (-a) := by
  unfold VF.Ge at *
  rwa [AddValuation.map_neg]

private theorem ge_one_lemma_5 : V.Ge 0 (1 : C) := by
  unfold VF.Ge
  rw [AddValuation.map_one]
  simp

private theorem ge_zero_lemma_6 (w : ℝ) : V.Ge w (0 : C) := by
  unfold VF.Ge
  rw [AddValuation.map_zero]
  exact le_top

private theorem ge_sum_lemma_7 {ι : Type} (s : Finset ι) {f : ι → C} {w : ℝ} (h : ∀ i ∈ s, V.Ge w (f i)) :
    V.Ge w (∑ i ∈ s, f i) := by
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact ge_zero_lemma_6 w
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact ge_add_lemma (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem ge0_pow_lemma_8 {a : C} (ha : V.Ge 0 a) (n : ℕ) : V.Ge 0 (a ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ge_one_lemma_5
  | succ n ih =>
    rw [pow_succ]
    have h := ge_mul_lemma_2 ih ha
    rwa [add_zero] at h

private theorem ge_l_lemma_9 : V.Ge 1 (V.l : C) := by
  unfold VF.Ge
  rw [V.v_l]
  simp

theorem Cg.refl (δ : ℝ) (x : C) : Cg V δ x x := by
  unfold Cg
  rw [sub_self]
  exact ge_zero_lemma_6 δ

theorem Cg.symm {δ : ℝ} {x y : C} (h : Cg V δ x y) : Cg V δ y x := by
  unfold Cg at *
  rw [← neg_sub]
  exact ge_neg_lemma_4 h

theorem Cg.trans {δ : ℝ} {x y z : C} (h1 : Cg V δ x y) (h2 : Cg V δ y z) : Cg V δ x z := by
  unfold Cg at *
  rw [← sub_add_sub_cancel x y z]
  exact ge_add_lemma h1 h2

theorem Cg.mono {δ δ' : ℝ} {x y : C} (h : Cg V δ x y) (hd : δ' ≤ δ) : Cg V δ' x y := by
  exact ge_mono_lemma_3 h hd

theorem valuation_ge_mul_of_nonneg {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge 0 b) : V.Ge w (a * b) := by
  have h := ge_mul_lemma_2 ha hb
  rwa [add_zero] at h

theorem Cg.mul {δ : ℝ} {x x' y y' : C} (hx : V.Ge 0 x) (hy' : V.Ge 0 y') (h1 : Cg V δ x x') (h2 : Cg V δ y y') :
    Cg V δ (x * y) (x' * y') := by
  unfold Cg at *
  have e : x * y - x' * y' = (y - y') * x + (x - x') * y' := by ring
  rw [e]
  exact ge_add_lemma (valuation_ge_mul_of_nonneg h2 hx) (valuation_ge_mul_of_nonneg h1 hy')

theorem Cg.pow {δ : ℝ} {x x' : C} (hx : V.Ge 0 x) (hx' : V.Ge 0 x') (h : Cg V δ x x') (n : ℕ) :
    Cg V δ (x ^ n) (x' ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact Cg.refl δ 1
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact Cg.mul (ge0_pow_lemma_8 hx n) hx' ih h

theorem Cg.sum {ι : Type} (s : Finset ι) {f g : ι → C} {δ : ℝ} (h : ∀ i ∈ s, Cg V δ (f i) (g i)) :
    Cg V δ (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact ge_sum_lemma_7 s h

theorem ge_prod {ι : Type} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) : V.Ge 0 (∏ i ∈ s, f i) := by
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty]
    exact ge_one_lemma_5
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    exact valuation_ge_mul_of_nonneg (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Cg.prod {ι : Type} (s : Finset ι) {f g : ι → C} (hf : ∀ i ∈ s, V.Ge 0 (f i)) (hg : ∀ i ∈ s, V.Ge 0 (g i))
    {δ : ℝ} (h : ∀ i ∈ s, Cg V δ (f i) (g i)) : Cg V δ (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  revert hf hg h
  refine Finset.induction_on s ?_ ?_
  · intro _ _ _
    rw [Finset.prod_empty, Finset.prod_empty]
    exact Cg.refl δ 1
  · intro a s ha ih hf hg h
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Cg.mul (hf a (Finset.mem_insert_self a s)) (ge_prod s fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem ne_zero_of_v {x : C} (hx : V.v x = 0) : x ≠ 0 := by
  intro h
  rw [h, AddValuation.map_zero] at hx
  exact WithTop.top_ne_zero hx

theorem valuation_nonneg_of_zero {x : C} (hx : V.v x = 0) : V.Ge 0 x := by
  unfold VF.Ge
  rw [hx]
  simp

theorem v_inv {x : C} (hx : V.v x = 0) : V.v x⁻¹ = 0 := by
  have h1 : V.v (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ (ne_zero_of_v hx), AddValuation.map_one]
  rwa [AddValuation.map_mul, hx, zero_add] at h1

theorem v_mul {x y : C} (hx : V.v x = 0) (hy : V.v y = 0) : V.v (x * y) = 0 := by
  rw [AddValuation.map_mul, hx, hy, add_zero]

theorem v_pow {x : C} (hx : V.v x = 0) (n : ℕ) : V.v (x ^ n) = 0 := by
  rw [AddValuation.map_pow, hx, smul_zero]

theorem ge_of_unit_mul {δ : ℝ} {u y : C} (hu : V.v u = 0) (h : V.Ge δ (u * y)) : V.Ge δ y := by
  unfold VF.Ge at *
  rwa [AddValuation.map_mul, hu, zero_add] at h

theorem ge_of_mul_unit {δ : ℝ} {u y : C} (hu : V.v u = 0) (h : V.Ge δ (y * u)) : V.Ge δ y := by
  unfold VF.Ge at *
  rwa [AddValuation.map_mul, hu, add_zero] at h

theorem Cg.inv {δ : ℝ} {x x' : C} (hx : V.v x = 0) (hx' : V.v x' = 0) (h : Cg V δ x x') : Cg V δ x⁻¹ x'⁻¹ := by
  have hne := ne_zero_of_v hx
  have hne' := ne_zero_of_v hx'
  have e : x⁻¹ - x'⁻¹ = (x' - x) * (x⁻¹ * x'⁻¹) := by field_simp <;> ring
  unfold Cg
  rw [e]
  exact valuation_ge_mul_of_nonneg (Cg.symm h) (valuation_nonneg_of_zero (v_mul (v_inv hx) (v_inv hx')))

theorem exists_ge_of_mm {x : C} (h : V.MM x) : ∃ δ : ℝ, 0 < δ ∧ V.Ge δ x := by
  by_cases ht : V.v x = ⊤
  · refine ⟨1, one_pos, ?_⟩
    unfold VF.Ge
    rw [ht]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
    unfold VF.MM at h
    rw [← hr] at h
    refine ⟨r, by exact_mod_cast h, ?_⟩
    unfold VF.Ge
    rw [← hr]

theorem exists_ge_of_mm_fin {ι : Type} [Fintype ι] (f : ι → C) (h : ∀ i, V.MM (f i)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i, V.Ge δ (f i) := by
  choose δs hpos hge using fun i => exists_ge_of_mm (h i)
  refine ⟨Finset.univ.fold min 1 δs, ?_, ?_, fun i => ?_⟩
  · exact (Finset.lt_fold_min _).2 ⟨one_pos, fun i _ => hpos i⟩
  · exact ((Finset.le_fold_min _).1 le_rfl).1
  · exact ge_mono_lemma_3 (hge i) (((Finset.le_fold_min _).1 le_rfl).2 i (Finset.mem_univ i))

theorem ge_pow_mul {δ : ℝ} {e : C} (h : V.Ge δ e) (n : ℕ) : V.Ge (n * δ) (e ^ n) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    exact ge_one_lemma_5
  | succ n ih =>
    rw [pow_succ]
    apply ge_mono_lemma_3 (ge_mul_lemma_2 ih h)
    push_cast
    linarith

theorem ge_natCast' (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact ge_zero_lemma_6 0
  | succ n ih =>
    rw [Nat.cast_succ]
    exact ge_add_lemma ih ge_one_lemma_5

theorem cg_one_pow_l {δ : ℝ} (hδ : 0 < δ) {e : C} (h : Cg V δ e 1) :
    Cg V (δ + min δ 1) (e ^ V.l) 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, e = t + 1 := ⟨e - 1, by ring⟩
  unfold Cg at *
  rw [add_sub_cancel_right] at h
  rw [add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  apply ge_sum_lemma_7
  intro m hm
  have hm' : m < V.l := Finset.mem_range.1 hm
  by_cases hml : m + 1 < V.l
  · obtain ⟨q, hq⟩ := V.l_prime.dvd_choose_self (Nat.succ_ne_zero m) hml
    rw [hq, Nat.cast_mul]
    have h1 : V.Ge ((m + 1 : ℕ) * δ) (t ^ (m + 1)) := ge_pow_mul h _
    have h2 : V.Ge 1 ((V.l : C) * (q : C)) := by
      have h3 := ge_mul_lemma_2 ge_l_lemma_9 (ge_natCast' (V := V) q)
      rwa [add_zero] at h3
    apply ge_mono_lemma_3 (ge_mul_lemma_2 h1 h2)
    have h4 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have h5 : min δ 1 ≤ 1 := min_le_right _ _
    nlinarith
  · have hml' : m + 1 = V.l := by omega
    rw [hml', Nat.choose_self, Nat.cast_one, mul_one]
    have h1 : V.Ge (V.l * δ) (t ^ V.l) := ge_pow_mul h _
    apply ge_mono_lemma_3 h1
    have h4 : (2 : ℝ) ≤ V.l := by exact_mod_cast V.l_prime.two_le
    have h5 : min δ 1 ≤ δ := min_le_left _ _
    nlinarith

theorem cg_one_pow_lk {δ : ℝ} (hδ : 0 < δ) {e : C} (h : Cg V δ e 1) (k : ℕ) :
    Cg V (δ + k * min δ 1) (e ^ (V.l ^ k)) 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hm : 0 < min δ 1 := lt_min hδ one_pos
    have hk : 0 < δ + k * min δ 1 := by positivity
    have h2 := cg_one_pow_l hk ih
    rw [pow_succ, pow_mul]
    apply Cg.mono h2
    have h3 : min δ 1 ≤ min (δ + k * min δ 1) 1 := by
      apply min_le_min _ le_rfl
      have : (0 : ℝ) ≤ k * min δ 1 := by positivity
      linarith
    push_cast
    linarith

theorem tendsto_pow_lk {δ : ℝ} (hδ : 0 < δ) {e ε : C} (_he : V.Ge 0 e) (hε : ε = 0 ∨ ε = 1) (h : Cg V δ e ε) :
    ∀ K : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, V.Ge K (ε - e ^ (V.l ^ k)) := by
  have hlt : ∀ k : ℕ, k < V.l ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      have := V.l_prime.two_le
      nlinarith
  intro K
  rcases hε with rfl | rfl
  · have he : V.Ge δ e := by
      have h' := h
      unfold Cg at h'
      rwa [sub_zero] at h'
    obtain ⟨k0, hk0⟩ := exists_nat_gt (K / δ)
    refine ⟨k0, fun k hk => ?_⟩
    rw [zero_sub]
    apply ge_neg_lemma_4
    apply ge_mono_lemma_3 (ge_pow_mul he (V.l ^ k))
    have h1 : (k : ℝ) < ((V.l ^ k : ℕ) : ℝ) := by exact_mod_cast hlt k
    have h2 : K / δ < ((V.l ^ k : ℕ) : ℝ) := by
      calc K / δ < k0 := hk0
        _ ≤ k := by exact_mod_cast hk
        _ < _ := h1
    rw [div_lt_iff₀ hδ] at h2
    linarith
  · have h1 := cg_one_pow_lk hδ h
    have hm : 0 < min δ 1 := lt_min hδ one_pos
    obtain ⟨k0, hk0⟩ := exists_nat_gt (K / min δ 1)
    refine ⟨k0, fun k hk => ?_⟩
    apply ge_mono_lemma_3 (Cg.symm (h1 k))
    have h2 : K / min δ 1 < k := lt_of_lt_of_le hk0 (by exact_mod_cast hk)
    rw [div_lt_iff₀ hm] at h2
    linarith

end IndAr

namespace IndAr

variable {C : Type} [Field C] {V : VF C}

theorem mm_add' {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [AddValuation.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  calc (0 : WithTop ℝ) < V.v a := ha
    _ = V.v a + 0 := (add_zero _).symm
    _ ≤ V.v a + V.v b := add_le_add le_rfl hb'

theorem mm_of_ge {δ : ℝ} (hδ : 0 < δ) {a : C} (h : V.Ge δ a) : V.MM a := by
  unfold VF.MM
  unfold VF.Ge at h
  exact lt_of_lt_of_le (by exact_mod_cast hδ) h

theorem mm_pow {a : C} (ha : V.MM a) (hi : V.Ge 0 a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  induction m with
  | zero => simpa using ha
  | succ m ih =>
    rw [pow_succ]
    exact mm_mul_int (ih (Nat.succ_ne_zero _)) hi

variable {O : Type} [CommRing O] {d : ℕ} [NeZero d]

theorem frob_cg (em : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (em a x)) (x : O) {δ : ℝ}
    (hδ : ∀ b : ZMod d, V.Ge δ (em (b + 1) x - em b x ^ V.l)) (b : ZMod d) (s : ℕ) :
    Cg V δ (em b x ^ (V.l ^ s)) (em (b + s) x) := by
  induction s with
  | zero =>
    simp only [pow_zero, pow_one, Nat.cast_zero, add_zero]
    exact Cg.refl δ _
  | succ s ih =>
    have h1 : Cg V δ ((em b x ^ (V.l ^ s)) ^ V.l) (em (b + s) x ^ V.l) :=
      Cg.pow (ge0_pow_lemma_8 (hint b x) _) (hint _ x) ih V.l
    have h2 : Cg V δ (em (b + s) x ^ V.l) (em (b + s + 1) x) := Cg.symm (hδ (b + s))
    rw [pow_succ, pow_mul, Nat.cast_succ, ← add_assoc]
    exact h1.trans h2

theorem units_of_sep (em : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (em a x)) (x : O) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ b : ZMod d, V.Ge δ (em (b + 1) x - em b x ^ V.l)) (b1 b2 : ZMod d)
    (h12 : V.v (em b1 x - em b2 x) = 0) (b : ZMod d) : V.v (em b x) = 0 := by
  by_contra hne
  have h0 : V.Ge 0 (em b x) := hint b x
  have hpos : V.MM (em b x) := by
    unfold VF.MM
    unfold VF.Ge at h0
    exact lt_of_le_of_ne (by simpa using h0) (Ne.symm hne)
  have hall : ∀ s : ℕ, V.MM (em (b + s) x) := by
    intro s
    induction s with
    | zero => simpa using hpos
    | succ s ih =>
      have e : em (b + ((s + 1 : ℕ) : ZMod d)) x =
          (em (b + s + 1) x - em (b + s) x ^ V.l) + em (b + s) x ^ V.l := by
        rw [Nat.cast_succ, ← add_assoc]
        ring
      rw [e]
      exact mm_add' (mm_of_ge hδ0 (hδ (b + s))) (mm_pow ih (hint _ x) V.l_prime.ne_zero)
  have hany : ∀ c : ZMod d, V.MM (em c x) := by
    intro c
    have h1 := hall (c - b).val
    rw [ZMod.natCast_zmod_val] at h1
    simpa using h1
  have hdiff : V.MM (em b1 x - em b2 x) := by
    rw [sub_eq_add_neg]
    refine mm_add' (hany b1) ?_
    unfold VF.MM
    rw [AddValuation.map_neg]
    exact hany b2
  unfold VF.MM at hdiff
  rw [h12] at hdiff
  exact lt_irrefl _ hdiff

end IndAr

namespace IndAr

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {d : ℕ} [NeZero d]

theorem Cg.neg {δ : ℝ} {x y : C} (h : Cg V δ x y) : Cg V δ (-x) (-y) := by
  unfold Cg at *
  rw [show -x - -y = -(x - y) by ring]
  exact ge_neg_lemma_4 h

def TT (d : ℕ) [NeZero d] : Finset (ZMod d × ZMod d) := Finset.univ.filter fun t => t.1 ≠ t.2

def fac (V : VF C) (em : ZMod d → O →+* C) (xs : ZMod d × ZMod d → O) (a b : ZMod d) (s : ℕ) (t : ZMod d × ZMod d) : C :=
  -(∑ j ∈ Finset.range (V.l ^ d - 1), (em b (xs t) * (em a (xs t))⁻¹ ^ (V.l ^ s)) ^ j)

theorem ge_l_pow_d : V.Ge 1 ((V.l : C) ^ d) := by
  have h := ge_pow_mul (ge_l_lemma_9 (V := V)) d
  apply ge_mono_lemma_3 h
  have : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  linarith

theorem cast_q : ((V.l ^ d - 1 : ℕ) : C) = (V.l : C) ^ d - 1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ V.l_prime.pos), Nat.cast_pow, Nat.cast_one]

theorem entry_cg (em : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (em a x)) (xs : ZMod d × ZMod d → O) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hfrob : ∀ t b, V.Ge δ (em (b + 1) (xs t) - em b (xs t) ^ V.l))
    (hsep : ∀ t : ZMod d × ZMod d, t.1 ≠ t.2 → V.v (em t.1 (xs t) - em t.2 (xs t)) = 0)
    (a b : ZMod d) (s : ℕ) :
    V.Ge 0 (∏ t ∈ TT d, fac V em xs a b s t) ∧
      Cg V δ (∏ t ∈ TT d, fac V em xs a b s t) (if b = a + (s : ZMod d) then 1 else 0) := by
  have hunit : ∀ t ∈ TT d, ∀ c : ZMod d, V.v (em c (xs t)) = 0 := by
    intro t ht c
    have ht' : t.1 ≠ t.2 := (Finset.mem_filter.1 ht).2
    exact units_of_sep em hint (xs t) hδ0 (hfrob t) t.1 t.2 (hsep t ht') c
  have hK : ∀ t ∈ TT d, Cg V δ (em b (xs t) * (em a (xs t))⁻¹ ^ (V.l ^ s))
      (em b (xs t) * (em (a + (s : ZMod d)) (xs t))⁻¹) := by
    intro t ht
    have hu := hunit t ht
    have h1 : Cg V δ ((em a (xs t)) ^ (V.l ^ s)) (em (a + (s : ZMod d)) (xs t)) :=
      frob_cg em hint (xs t) (hfrob t) a s
    have h2 : Cg V δ ((em a (xs t)) ^ (V.l ^ s))⁻¹ (em (a + (s : ZMod d)) (xs t))⁻¹ :=
      Cg.inv (v_pow (hu a) _) (hu _) h1
    rw [inv_pow]
    exact Cg.mul (hint b (xs t)) (valuation_nonneg_of_zero (v_inv (hu _))) (Cg.refl δ _) h2
  have hKint : ∀ t ∈ TT d, V.Ge 0 (em b (xs t) * (em a (xs t))⁻¹ ^ (V.l ^ s)) := fun t ht =>
    valuation_ge_mul_of_nonneg (hint b (xs t)) (ge0_pow_lemma_8 (valuation_nonneg_of_zero (v_inv (hunit t ht a))) _)
  have hfac_int : ∀ t ∈ TT d, V.Ge 0 (fac V em xs a b s t) := by
    intro t ht
    unfold fac
    apply ge_neg_lemma_4
    apply ge_sum_lemma_7
    intro j _
    exact ge0_pow_lemma_8 (hKint t ht) j
  refine ⟨ge_prod _ hfac_int, ?_⟩
  split_ifs with hb
  · have hone : ∀ t ∈ TT d, Cg V δ (fac V em xs a b s t) 1 := by
      intro t ht
      have hu := hunit t ht
      have hr : em b (xs t) * (em (a + (s : ZMod d)) (xs t))⁻¹ = 1 := by
        rw [hb]
        exact mul_inv_cancel₀ (ne_zero_of_v (hu _))
      have hK1 := hK t ht
      rw [hr] at hK1
      have hs : Cg V δ (∑ j ∈ Finset.range (V.l ^ d - 1), (em b (xs t) * (em a (xs t))⁻¹ ^ (V.l ^ s)) ^ j)
          (∑ j ∈ Finset.range (V.l ^ d - 1), (1 : C) ^ j) :=
        Cg.sum _ fun j _ => Cg.pow (hKint t ht) ge_one_lemma_5 hK1 j
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
      rw [cast_q] at hs
      have h2 : Cg V δ (-((V.l : C) ^ d - 1)) 1 := by
        unfold Cg
        rw [show -((V.l : C) ^ d - 1) - 1 = -((V.l : C) ^ d) by ring]
        exact ge_neg_lemma_4 (ge_mono_lemma_3 ge_l_pow_d hδ1)
      exact (Cg.neg hs).trans h2
    have h3 := Cg.prod (TT d) (fun t ht => hfac_int t ht) (fun _ _ => ge_one_lemma_5) hone
    rwa [Finset.prod_const_one] at h3
  · set t0 : ZMod d × ZMod d := (b, a + (s : ZMod d)) with ht0def
    have ht0 : t0 ∈ TT d := by simp [TT, t0, hb]
    have hu := hunit t0 ht0
    have hq : ∀ c, Cg V δ ((em c (xs t0)) ^ (V.l ^ d - 1)) 1 := by
      intro c
      have h1 := frob_cg em hint (xs t0) (hfrob t0) c d
      rw [ZMod.natCast_self, add_zero] at h1
      have hpos : 1 ≤ V.l ^ d := Nat.one_le_pow _ _ V.l_prime.pos
      have e : (em c (xs t0)) ^ (V.l ^ d) - em c (xs t0) =
          em c (xs t0) * ((em c (xs t0)) ^ (V.l ^ d - 1) - 1) := by
        conv_lhs => rw [show V.l ^ d = (V.l ^ d - 1) + 1 by omega, pow_succ]
        ring
      unfold Cg at h1 ⊢
      rw [e] at h1
      exact ge_of_unit_mul (hu c) h1
    obtain ⟨r, hr⟩ : ∃ r : C, em b (xs t0) * (em (a + (s : ZMod d)) (xs t0))⁻¹ = r := ⟨_, rfl⟩
    have hKt : Cg V δ (em b (xs t0) * (em a (xs t0))⁻¹ ^ (V.l ^ s)) r := by
      rw [← hr]
      exact hK t0 ht0
    have hrn : Cg V δ (r ^ (V.l ^ d - 1)) 1 := by
      rw [← hr, mul_pow, inv_pow]
      have h2 : Cg V δ ((em (a + (s : ZMod d)) (xs t0)) ^ (V.l ^ d - 1))⁻¹ (1 : C)⁻¹ :=
        Cg.inv (v_pow (hu _) _) (by rw [AddValuation.map_one]) (hq (a + s))
      rw [inv_one] at h2
      have h3 := Cg.mul (ge0_pow_lemma_8 (hint _ _) _) ge_one_lemma_5 (hq b) h2
      rwa [mul_one] at h3
    have hne := ne_zero_of_v (hu (a + (s : ZMod d)))
    have hr1 : V.v (r - 1) = 0 := by
      have e : r - 1 = (em b (xs t0) - em (a + (s : ZMod d)) (xs t0)) * (em (a + (s : ZMod d)) (xs t0))⁻¹ := by
        rw [← hr, sub_mul, mul_inv_cancel₀ hne]
      rw [e, AddValuation.map_mul, hsep t0 hb, v_inv (hu _), add_zero]
    have hrint : V.Ge 0 r := valuation_nonneg_of_zero (by rw [← hr, AddValuation.map_mul, hu b, v_inv (hu _), add_zero])
    have hgs : V.Ge δ (∑ j ∈ Finset.range (V.l ^ d - 1), r ^ j) := by
      have h1 : V.Ge δ ((∑ j ∈ Finset.range (V.l ^ d - 1), r ^ j) * (r - 1)) := by
        rw [geom_sum_mul]
        exact hrn
      exact ge_of_mul_unit hr1 h1
    have hsum := Cg.sum (Finset.range (V.l ^ d - 1)) fun j _ => Cg.pow (hKint t0 ht0) hrint hKt j
    have hfac0 : V.Ge δ (fac V em xs a b s t0) := by
      have h3 := ge_add_lemma hsum hgs
      rw [sub_add_cancel] at h3
      exact ge_neg_lemma_4 h3
    unfold Cg
    rw [sub_zero, ← Finset.mul_prod_erase (TT d) (fun t => fac V em xs a b s t) ht0]
    exact valuation_ge_mul_of_nonneg hfac0 (ge_prod _ fun t ht => hfac_int t (Finset.mem_of_mem_erase ht))

end IndAr

namespace IndAr

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {d : ℕ} [NeZero d]

theorem ind_gen (em : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (em a x))
    (hfr : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l))
    (hsp : ∀ a a' : ZMod d, a ≠ a' → ∃ x, V.v (em a x - em a' x) = 0)
    (N : Type) (ty : N → ZMod d) (M : Set (ℕ → N → C))
    (h1 : 1 ∈ M) (hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M) (hneg : ∀ m, m ∈ M → -m ∈ M)
    (hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M)
    (hteich : ∀ c : C, V.Ge 0 c → (fun s (_ : N) => c ^ (V.l ^ s)) ∈ M)
    (hact : ∀ α : O, (fun (_ : ℕ) n => em (ty n) α) ∈ M)
    (hlim : ∀ (m : ℕ → ℕ → N → C) (m' : ℕ → N → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M)
    (a : ZMod d) : (fun (s : ℕ) (n : N) => if ty n = a + (s : ZMod d) then (1 : C) else 0) ∈ M := by
  have hsp' : ∀ t : ZMod d × ZMod d, ∃ x : O, t.1 ≠ t.2 → V.v (em t.1 x - em t.2 x) = 0 := by
    intro t
    by_cases h : t.1 = t.2
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨x, hx⟩ := hsp t.1 t.2 h
      exact ⟨x, fun _ => hx⟩
  choose xs hxs using hsp'
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_ge_of_mm_fin
    (fun q : (ZMod d × ZMod d) × ZMod d => em (q.2 + 1) (xs q.1) - em q.2 (xs q.1) ^ V.l)
    (fun q => hfr _ _)
  have hfrob : ∀ t b, V.Ge δ (em (b + 1) (xs t) - em b (xs t) ^ V.l) := fun t b => hδ (t, b)
  have h0 : (0 : ℕ → N → C) ∈ M := by
    have h2 := hadd 1 (-1) h1 (hneg 1 h1)
    rwa [add_neg_cancel] at h2
  have hpowM : ∀ m, m ∈ M → ∀ j : ℕ, m ^ j ∈ M := by
    intro m hm j
    induction j with
    | zero =>
      rw [pow_zero]
      exact h1
    | succ j ih =>
      rw [pow_succ]
      exact hmul _ _ ih hm
  have hsumM : ∀ (s : Finset ℕ) (f : ℕ → ℕ → N → C), (∀ j ∈ s, f j ∈ M) → (∑ j ∈ s, f j) ∈ M := by
    intro s f
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.sum_empty]
      exact h0
    · intro j s hj ih hf
      rw [Finset.sum_insert hj]
      exact hadd _ _ (hf j (Finset.mem_insert_self j s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have hprodM : ∀ (s : Finset (ZMod d × ZMod d)) (f : ZMod d × ZMod d → ℕ → N → C),
      (∀ i ∈ s, f i ∈ M) → (∏ i ∈ s, f i) ∈ M := by
    intro s f
    refine Finset.induction_on s ?_ ?_
    · intro _
      rw [Finset.prod_empty]
      exact h1
    · intro j s hj ih hf
      rw [Finset.prod_insert hj]
      exact hmul _ _ (hf j (Finset.mem_insert_self j s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  let mfac : ZMod d × ZMod d → ℕ → N → C := fun t s n => fac V em xs a (ty n) s t
  have hmfac : ∀ t ∈ TT d, mfac t ∈ M := by
    intro t ht
    have ht' : t.1 ≠ t.2 := (Finset.mem_filter.1 ht).2
    have hu : V.v (em a (xs t)) = 0 := units_of_sep em hint (xs t) hδ0 (hfrob t) t.1 t.2 (hxs t ht') a
    have e : mfac t = -(∑ j ∈ Finset.range (V.l ^ d - 1),
        ((fun (_ : ℕ) (n : N) => em (ty n) (xs t)) *
          (fun (s : ℕ) (_ : N) => ((em a (xs t))⁻¹) ^ (V.l ^ s))) ^ j) := by
      funext s n
      simp only [mfac, fac, Pi.neg_apply, Finset.sum_apply, Pi.pow_apply, Pi.mul_apply]
    rw [e]
    apply hneg
    apply hsumM
    intro j _
    apply hpowM
    exact hmul _ _ (hact _) (hteich _ (valuation_nonneg_of_zero (v_inv hu)))
  let P : ℕ → N → C := ∏ t ∈ TT d, mfac t
  have hP : P ∈ M := hprodM (TT d) mfac hmfac
  have hPsn : ∀ s n, P s n = ∏ t ∈ TT d, fac V em xs a (ty n) s t := by
    intro s n
    simp only [P, mfac, Finset.prod_apply]
  refine hlim (fun k => P ^ (V.l ^ k)) _ (fun k => hpowM P hP _) ?_
  intro K s n
  obtain ⟨hint0, hcg⟩ := entry_cg em hint xs hδ0 hδ1 hfrob hxs a (ty n) s
  have hε : (if ty n = a + (s : ZMod d) then (1 : C) else 0) = 0 ∨
      (if ty n = a + (s : ZMod d) then (1 : C) else 0) = 1 := by
    split_ifs <;> simp
  obtain ⟨k0, hk0⟩ := tendsto_pow_lk hδ0 hint0 hε hcg K
  refine ⟨k0, fun k hk => ?_⟩
  simp only [Pi.pow_apply]
  rw [hPsn]
  exact hk0 k hk

end IndAr

theorem indSt_holds : IndSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g N ty M h1 hadd hneg hmul hteich hact hlim a
  exact IndAr.ind_gen (p.em g) (p.em_int g) (p.em_frob g)
    (fun b b' h => p.em_sep (g, b) (g, b') (by simp [h])) N ty M h1 hadd hneg hmul hteich hact hlim a

theorem typical_averaging_of_limits (hAct : OActTySt) (hLim : LimTySt) : PTAvgFBSt := by
  exact ptAvg_of hAct hLim indSt_holds

end Formalism.L2.FormalSeriesBounds
