import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

open Filter

section WeakApproxAux

variable {F : Type*} [Field F]

theorem wa_exists_coe (w : AddValuation F (WithTop ℤ)) (hw : ∀ a : F, a ≠ 0 → w a ≠ ⊤) {a : F}
    (ha : a ≠ 0) : ∃ m : ℤ, w a = m := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hw a ha)
  exact ⟨m, hm.symm⟩

theorem wa_ne_zero_of_coe (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (h : w a = m) :
    a ≠ 0 := by
  rintro rfl
  rw [AddValuation.map_zero] at h
  exact WithTop.top_ne_coe h

theorem wa_pow (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (h : w a = m) (n : ℕ) :
    w (a ^ n) = ((n * m : ℤ) : WithTop ℤ) := by
  induction n with
  | zero =>
    rw [pow_zero, AddValuation.map_one]
    simp
  | succ k ih =>
    rw [pow_succ, AddValuation.map_mul, ih, h, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

theorem wa_mul (w : AddValuation F (WithTop ℤ)) {a b : F} {m n : ℤ} (ha : w a = m)
    (hb : w b = n) : w (a * b) = ((m + n : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_mul, ha, hb, ← WithTop.coe_add]

theorem wa_inv (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (ha : w a = m) :
    w a⁻¹ = ((-m : ℤ) : WithTop ℤ) := by
  have ha0 : a ≠ 0 := wa_ne_zero_of_coe w ha
  have h1 : w (a⁻¹ * a) = 0 := by rw [inv_mul_cancel₀ ha0, AddValuation.map_one]
  rw [AddValuation.map_mul, ha] at h1
  have hne : w a⁻¹ ≠ ⊤ := by
    intro ht
    rw [ht, WithTop.top_add, ← WithTop.coe_zero] at h1
    exact WithTop.top_ne_coe h1
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hc] at h1 ⊢
  have h2 : c + m = 0 := by exact_mod_cast h1
  rw [show c = -m by omega]

theorem wa_div (w : AddValuation F (WithTop ℤ)) {a b : F} {m n : ℤ} (ha : w a = m)
    (hb : w b = n) : w (a / b) = ((m - n : ℤ) : WithTop ℤ) := by
  rw [div_eq_mul_inv, wa_mul w ha (wa_inv w hb), sub_eq_add_neg]

theorem wa_zpow (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (h : w a = m) (z : ℤ) :
    w (a ^ z) = ((z * m : ℤ) : WithTop ℤ) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [zpow_natCast, wa_pow w h n]
  · rw [zpow_neg, zpow_natCast, wa_inv w (wa_pow w h n)]
    congr 1
    ring

theorem wa_prod {ι : Type*} (w : AddValuation F (WithTop ℤ)) (S : Finset ι) (f : ι → F)
    (e : ι → ℤ) (h : ∀ i ∈ S, w (f i) = e i) :
    w (∏ i ∈ S, f i) = ((∑ i ∈ S, e i : ℤ) : WithTop ℤ) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one, WithTop.coe_zero]
  · intro j S hj ih h
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact wa_mul w (h j (Finset.mem_insert_self j S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem exists_pos_neg_valuation (A B : AddValuation F (WithTop ℤ)) {z x : F} {a b m n : ℤ}
    (hza : A z = a) (hzb : B z = b) (hxa : A x = m) (hxb : B x = n) (ha : 0 < a) (hm : 0 ≤ m)
    (hn : n < 0) : ∃ y : F, ∃ c d : ℤ, A y = c ∧ B y = d ∧ 0 < c ∧ d < 0 := by
  refine ⟨z * x ^ (b.toNat + 1), _, _, wa_mul A hza (wa_pow A hxa _),
    wa_mul B hzb (wa_pow B hxb _), ?_, ?_⟩
  · have h1 : (0 : ℤ) ≤ ((b.toNat + 1 : ℕ) : ℤ) * m := mul_nonneg (by positivity) hm
    linarith
  · have h1 := Int.self_le_toNat b
    have h2 : (0 : ℤ) ≤ ((b.toNat + 1 : ℕ) : ℤ) * (-1 - n) := mul_nonneg (by positivity) (by omega)
    have h3 : ((b.toNat + 1 : ℕ) : ℤ) = (b.toNat : ℤ) + 1 := Nat.cast_succ b.toNat
    nlinarith

theorem wa_eq_of_le (v w : AddValuation F (WithTop ℤ)) (hv : ∀ a : F, a ≠ 0 → v a ≠ ⊤)
    (hw : ∀ a : F, a ≠ 0 → w a ≠ ⊤) (hv1 : ∃ π : F, v π = 1) (hw1 : ∃ ρ : F, w ρ = 1)
    (h : ∀ a, 0 < v a → 0 ≤ w a) : v = w := by
  obtain ⟨q, hq⟩ := hv1
  obtain ⟨q', hq'⟩ := hw1
  have hq1 : v q = ((1 : ℤ) : WithTop ℤ) := by rw [WithTop.coe_one]; exact hq
  have hq1' : w q' = ((1 : ℤ) : WithTop ℤ) := by rw [WithTop.coe_one]; exact hq'
  have hq0 : q ≠ 0 := wa_ne_zero_of_coe v hq1
  have hq0' : q' ≠ 0 := wa_ne_zero_of_coe w hq1'
  obtain ⟨p, hp⟩ := wa_exists_coe w hw hq0
  obtain ⟨r, hr⟩ := wa_exists_coe v hv hq0'
  have key : ∀ x : F, ∀ m n : ℤ, v x = m → w x = n → (0 ≤ m ↔ 0 ≤ n) := by
    intro x m n hm hn
    constructor
    · intro hm0
      by_contra hn0
      push_neg at hn0
      obtain ⟨y, c, d, hc, hd, hc0, hd0⟩ := exists_pos_neg_valuation v w hq1 hp hm hn one_pos hm0 hn0
      have hy := h y (by rw [hc, ← WithTop.coe_zero, WithTop.coe_lt_coe]; exact hc0)
      rw [hd, ← WithTop.coe_zero, WithTop.coe_le_coe] at hy
      omega
    · intro hn0
      by_contra hm0
      push_neg at hm0
      obtain ⟨y, c, d, hc, hd, hc0, hd0⟩ := exists_pos_neg_valuation w v hq1' hr hn hm one_pos hn0 hm0
      have hy := h y⁻¹ (by rw [wa_inv v hd, ← WithTop.coe_zero, WithTop.coe_lt_coe]; omega)
      rw [wa_inv w hc, ← WithTop.coe_zero, WithTop.coe_le_coe] at hy
      omega
  have hunit : ∀ t : F, ∀ d : ℤ, v t = ((0 : ℤ) : WithTop ℤ) → w t = d → d = 0 := by
    intro t d hv0 hwd
    have h1 := (key t 0 d hv0 hwd).mp le_rfl
    have h2 := (key t⁻¹ (-0) (-d) (wa_inv v hv0) (wa_inv w hwd)).mp (by norm_num)
    omega
  have hmul : ∀ x : F, ∀ m n : ℤ, v x = m → w x = n → n = m * p := by
    intro x m n hm hn
    have hv0 := wa_div v hm (wa_zpow v hq1 m)
    have hw0 := wa_div w hn (wa_zpow w hp m)
    have h1 := hunit _ _ (by rw [hv0]; congr 1; ring) hw0
    linarith
  have hp1 : p = 1 := by
    have h1 := hmul q' r 1 hr hq1'
    have h2 := (key q 1 p hq1 hp).mp zero_le_one
    have h3 := (key q' r 1 hr hq1').mpr zero_le_one
    have h4 : p ≠ 0 := by rintro rfl; simp at h1
    have h5 : r ≠ 0 := by rintro rfl; simp at h1
    have h6 : 1 ≤ p := by omega
    have h7 : 1 ≤ r := by omega
    nlinarith
  refine AddValuation.ext fun x => ?_
  by_cases hx : x = 0
  · rw [hx, AddValuation.map_zero, AddValuation.map_zero]
  · obtain ⟨m, hm⟩ := wa_exists_coe v hv hx
    obtain ⟨n, hn⟩ := wa_exists_coe w hw hx
    rw [hm, hn, hmul x m n hm hn, hp1, mul_one]

theorem wa_pair (v w : AddValuation F (WithTop ℤ)) (hv : ∀ a : F, a ≠ 0 → v a ≠ ⊤)
    (hw : ∀ a : F, a ≠ 0 → w a ≠ ⊤) (hv1 : ∃ π : F, v π = 1) (hw1 : ∃ ρ : F, w ρ = 1)
    (hne : v ≠ w) : ∃ s, 0 < v s ∧ w s < 0 := by
  by_contra hcon
  push_neg at hcon
  exact hne (wa_eq_of_le v w hv hw hv1 hw1 hcon)

private theorem addValuation_add_eq_of_lt (w : AddValuation F (WithTop ℤ)) {x y : F} (h : w x < w y) :
    w (x + y) = w x := by
  rw [AddValuation.map_add_of_distinct_val w h.ne, min_eq_left h.le]

private theorem addValuation_one_add_pow_of_pos (w : AddValuation F (WithTop ℤ)) {s : F} {a : ℤ} (hs : w s = a)
    (M : ℕ) (hM : 0 < M) (ha : 0 < a) : w (1 + s ^ M) = ((0 : ℤ) : WithTop ℤ) := by
  have h1 := wa_pow w hs M
  have h2 : w 1 < w (s ^ M) := by
    rw [h1, AddValuation.map_one, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    exact mul_pos (by exact_mod_cast hM) ha
  rw [addValuation_add_eq_of_lt w h2, AddValuation.map_one, WithTop.coe_zero]

private theorem addValuation_one_add_pow_of_neg (w : AddValuation F (WithTop ℤ)) {s : F} {a : ℤ} (hs : w s = a)
    (M : ℕ) (hM : 0 < M) (ha : a < 0) : w (1 + s ^ M) = ((↑M * a : ℤ) : WithTop ℤ) := by
  have h1 := wa_pow w hs M
  have h2 : w (s ^ M) < w 1 := by
    rw [h1, AddValuation.map_one, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hM) ha
  rw [add_comm, addValuation_add_eq_of_lt w h2, h1]

private theorem exists_nat_gt_of_finset {ι : Type*} (T : Finset ι) (c : ι → ℤ) :
    ∃ N : ℕ, ∀ j ∈ T, c j < N := by
  refine ⟨(∑ j ∈ T, (c j).toNat) + 1, fun j hj => ?_⟩
  have h1 := Int.self_le_toNat (c j)
  have h2 : (c j).toNat ≤ ∑ j ∈ T, (c j).toNat :=
    Finset.single_le_sum (f := fun j => (c j).toNat) (fun _ _ => Nat.zero_le _) hj
  have h3 : ((c j).toNat : ℤ) ≤ ((∑ j ∈ T, (c j).toNat : ℕ) : ℤ) := Nat.cast_le.mpr h2
  rw [Nat.cast_succ]
  linarith

theorem wa_sep {ι : Type*} [DecidableEq ι] (v : ι → AddValuation F (WithTop ℤ))
    (hfin : ∀ i (a : F), a ≠ 0 → v i a ≠ ⊤) (hone : ∀ i, ∃ π : F, v i π = 1)
    (hdist : Pairwise fun i j => v i ≠ v j) (i : ι) (T : Finset ι) (hi : i ∉ T) :
    ∃ s : F, s ≠ 0 ∧ 0 < v i s ∧ ∀ j ∈ T, v j s < 0 := by
  revert hi
  refine Finset.induction_on T ?_ ?_
  · intro _
    obtain ⟨q, hq⟩ := hone i
    have hq1 : v i q = ((1 : ℤ) : WithTop ℤ) := by rw [WithTop.coe_one]; exact hq
    refine ⟨q, wa_ne_zero_of_coe (v i) hq1, ?_, ?_⟩
    · rw [hq1, ← WithTop.coe_zero, WithTop.coe_lt_coe]
      exact one_pos
    · intro j hj
      simp at hj
  · intro j T hjT ih hi
    have hij : i ≠ j := by
      rintro rfl
      exact hi (Finset.mem_insert_self _ _)
    have hiT : i ∉ T := fun h => hi (Finset.mem_insert_of_mem h)
    obtain ⟨s, hs0, hsi, hsT⟩ := ih hiT
    obtain ⟨t, hti, htj⟩ := wa_pair (v i) (v j) (hfin i) (hfin j) (hone i) (hone j) (hdist hij)
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [AddValuation.map_zero] at htj
      exact absurd htj (not_lt.mpr le_top)
    choose a ha using fun l => wa_exists_coe (v l) (hfin l) hs0
    choose c hc using fun l => wa_exists_coe (v l) (hfin l) ht0
    have hai : 0 < a i := by
      have h' := hsi
      rw [ha i, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
      exact h'
    have hci : 0 < c i := by
      have h' := hti
      rw [hc i, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
      exact h'
    have hcj : c j < 0 := by
      have h' := htj
      rw [hc j, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
      exact h'
    have haT : ∀ l ∈ T, a l < 0 := by
      intro l hl
      have h' := hsT l hl
      rw [ha l, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
      exact h'
    obtain ⟨N1, hN1⟩ := exists_nat_gt_of_finset T c
    obtain ⟨N2, hN2⟩ := exists_nat_gt_of_finset T (fun l => -c l)
    by_cases hajle : a j ≤ 0
    · have hv : ∀ l, v l (s ^ N1 * t) = ((↑N1 * a l + c l : ℤ) : WithTop ℤ) :=
        fun l => wa_mul (v l) (wa_pow (v l) (ha l) N1) (hc l)
      refine ⟨s ^ N1 * t, wa_ne_zero_of_coe (v i) (hv i), ?_, ?_⟩
      · rw [hv i, ← WithTop.coe_zero, WithTop.coe_lt_coe]
        have h0 : (0 : ℤ) ≤ (N1 : ℤ) * a i := mul_nonneg (by positivity) hai.le
        linarith
      · intro l hl
        rw [hv l, ← WithTop.coe_zero, WithTop.coe_lt_coe]
        rcases Finset.mem_insert.mp hl with hlj | hlT
        · rw [hlj]
          have h0 : (N1 : ℤ) * a j ≤ 0 := by nlinarith [(by positivity : (0 : ℤ) ≤ (N1 : ℤ))]
          linarith
        · have hb : c l < (N1 : ℤ) := hN1 l hlT
          have hal := haT l hlT
          have h0 : (0 : ℤ) ≤ (N1 : ℤ) * (-1 - a l) := mul_nonneg (by positivity) (by omega)
          nlinarith
    · have hajpos : 0 < a j := by omega
      have hM : 0 < N2 + 1 := Nat.succ_pos N2
      have hDi := addValuation_one_add_pow_of_pos (v i) (ha i) (N2 + 1) hM hai
      have hDj := addValuation_one_add_pow_of_pos (v j) (ha j) (N2 + 1) hM hajpos
      have hti' := wa_mul (v i) (hc i) (wa_inv (v i) hDi)
      have htj' := wa_mul (v j) (hc j) (wa_inv (v j) hDj)
      have hltj : v j (t * (1 + s ^ (N2 + 1))⁻¹) < v j s := by
        rw [htj', ha j, WithTop.coe_lt_coe]
        omega
      have hj : v j (s + t * (1 + s ^ (N2 + 1))⁻¹) = ((c j + -0 : ℤ) : WithTop ℤ) := by
        rw [add_comm, addValuation_add_eq_of_lt (v j) hltj, htj']
      refine ⟨s + t * (1 + s ^ (N2 + 1))⁻¹, wa_ne_zero_of_coe (v j) hj, ?_, ?_⟩
      · refine lt_of_lt_of_le (lt_min hsi ?_) (AddValuation.map_add (v i) _ _)
        rw [hti', ← WithTop.coe_zero, WithTop.coe_lt_coe]
        omega
      · intro l hl
        rcases Finset.mem_insert.mp hl with hlj | hlT
        · rw [hlj, hj, ← WithTop.coe_zero, WithTop.coe_lt_coe]
          omega
        · have hal := haT l hlT
          have hDl := addValuation_one_add_pow_of_neg (v l) (ha l) (N2 + 1) hM hal
          have htl' := wa_mul (v l) (hc l) (wa_inv (v l) hDl)
          have hb : -c l < (N2 : ℤ) := hN2 l hlT
          have hlt : v l s < v l (t * (1 + s ^ (N2 + 1))⁻¹) := by
            rw [ha l, htl', WithTop.coe_lt_coe]
            have h0 : (0 : ℤ) ≤ ((N2 + 1 : ℕ) : ℤ) * (-1 - a l) :=
              mul_nonneg (by positivity) (by omega)
            have h3 : ((N2 + 1 : ℕ) : ℤ) = (N2 : ℤ) + 1 := Nat.cast_succ N2
            nlinarith
          rw [addValuation_add_eq_of_lt (v l) hlt, ha l, ← WithTop.coe_zero, WithTop.coe_lt_coe]
          exact hal

end WeakApproxAux

private theorem lt_addValuation_sum_of_forall_lt {F : Type*} [Field F] {ι : Type*} (w : AddValuation F (WithTop ℤ))
    (S : Finset ι) (x : ι → F) (c : WithTop ℤ) (h : ∀ i ∈ S, c < w (x i)) (hc : c ≠ ⊤) :
    c < w (∑ i ∈ S, x i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    rw [Finset.sum_empty, AddValuation.map_zero]
    exact lt_top_iff_ne_top.mpr hc
  · intro j S hjS ih h
    rw [Finset.sum_insert hjS]
    exact lt_of_lt_of_le (lt_min (h j (Finset.mem_insert_self j S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) (AddValuation.map_add w _ _)

theorem weak_approx_orders {F : Type*} [Field F] {k : ℕ} (v : Fin k → AddValuation F (WithTop ℤ))
    (hfin : ∀ i (a : F), a ≠ 0 → v i a ≠ ⊤) (hone : ∀ i, ∃ π : F, v i π = 1)
    (hdist : Pairwise fun i j => v i ≠ v j) (n : Fin k → ℤ) :
    ∃ g : F, ∀ i, v i g = n i := by
  choose s hs0 hsi hsj using
    fun i => wa_sep v hfin hone hdist i (Finset.univ.erase i) (by simp)
  choose q hq using hone
  have hq1 : ∀ i, v i (q i) = ((1 : ℤ) : WithTop ℤ) := fun i => by
    rw [WithTop.coe_one]
    exact hq i
  have hq0 : ∀ i, q i ≠ 0 := fun i => wa_ne_zero_of_coe (v i) (hq1 i)
  choose p hp using fun i j => wa_exists_coe (v j) (hfin j) (hq0 i)
  choose a ha using fun i j => wa_exists_coe (v j) (hfin j) (hs0 i)
  have hai : ∀ i, 0 < a i i := fun i => by
    have h' := hsi i
    rw [ha i i, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
    exact h'
  have haij : ∀ i j, i ≠ j → a i j < 0 := fun i j hij => by
    have h' := hsj i j (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    rw [ha i j, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
    exact h'
  choose N hN using fun i => exists_nat_gt_of_finset (Finset.univ : Finset (Fin k)) (fun j => n j - n i * p i j)
  have hdiag : ∀ i, v i (q i ^ n i * (1 + s i ^ (N i + 1))⁻¹) = ((n i : ℤ) : WithTop ℤ) := by
    intro i
    rw [wa_mul (v i) (wa_zpow (v i) (hq1 i) (n i))
      (wa_inv (v i) (addValuation_one_add_pow_of_pos (v i) (ha i i) (N i + 1) (Nat.succ_pos _) (hai i)))]
    congr 1
    ring
  have hoff : ∀ i j, i ≠ j →
      ((n j : ℤ) : WithTop ℤ) < v j (q i ^ n i * (1 + s i ^ (N i + 1))⁻¹) := by
    intro i j hij
    have hneg : a i j < 0 := haij i j hij
    rw [wa_mul (v j) (wa_zpow (v j) (hp i j) (n i))
      (wa_inv (v j) (addValuation_one_add_pow_of_neg (v j) (ha i j) (N i + 1) (Nat.succ_pos _) hneg)),
      WithTop.coe_lt_coe]
    have hb : n j - n i * p i j < (N i : ℤ) := hN i j (Finset.mem_univ j)
    have h0 : (0 : ℤ) ≤ ((N i + 1 : ℕ) : ℤ) * (-1 - a i j) := mul_nonneg (by positivity) (by omega)
    have h3 : ((N i + 1 : ℕ) : ℤ) = (N i : ℤ) + 1 := Nat.cast_succ (N i)
    nlinarith
  refine ⟨∑ i, q i ^ n i * (1 + s i ^ (N i + 1))⁻¹, fun j => ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hrest : ((n j : ℤ) : WithTop ℤ) <
      v j (∑ i ∈ Finset.univ.erase j, q i ^ n i * (1 + s i ^ (N i + 1))⁻¹) :=
    lt_addValuation_sum_of_forall_lt (v j) _ _ _ (fun i hi => hoff i j (Finset.ne_of_mem_erase hi)) WithTop.coe_ne_top
  have hlt : v j (q j ^ n j * (1 + s j ^ (N j + 1))⁻¹) <
      v j (∑ i ∈ Finset.univ.erase j, q i ^ n i * (1 + s i ^ (N i + 1))⁻¹) := by
    rw [hdiag j]
    exact hrest
  rw [addValuation_add_eq_of_lt (v j) hlt, hdiag j]

end ReciprocityTheory.ChartRestriction.G.T0
