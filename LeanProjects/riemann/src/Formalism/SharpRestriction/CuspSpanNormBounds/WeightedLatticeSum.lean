import Mathlib

noncomputable section

namespace Formalism.MainNotions.WeightedLatticeSum

open Finset

def wt (R : ℝ) (m : ℕ) : ℝ := (max 1 (((m : ℝ) - 1) / (2 * R))) ^ (-(3 / 2 : ℝ))

lemma rpow_neg_three_halves {t : ℝ} (ht : 0 < t) : t ^ (-(3 / 2 : ℝ)) = 1 / (t * Real.sqrt t) := by
  rw [Real.rpow_neg ht.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
    ← Real.sqrt_eq_rpow, one_div]

lemma wt_nonneg (R : ℝ) (m : ℕ) : 0 ≤ wt R m := by
  unfold wt
  exact Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

lemma wt_le_one (R : ℝ) (m : ℕ) : wt R m ≤ 1 := by
  unfold wt
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by norm_num)

private theorem inv_mul_le_two_mul_inv_sub_inv_of_sq (k a b : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ha2 : a ^ 2 = k)
    (hb2 : b ^ 2 = k - 1) : 1 / (k * a) ≤ 2 * (1 / b - 1 / a) := by
  have hba : b ≤ a := by nlinarith
  have hab : (a - b) * (a + b) = 1 := by linear_combination ha2 - hb2
  have hD : 0 < a * b * (a + b) := mul_pos (mul_pos ha0 hb0) (add_pos ha0 hb0)
  have e : 2 * (1 / b - 1 / a) = 2 / (a * b * (a + b)) := by
    apply eq_div_of_mul_eq hD.ne'
    calc 2 * (1 / b - 1 / a) * (a * b * (a + b))
        = 2 * ((1 / b * b) * a - (1 / a * a) * b) * (a + b) := by ring
      _ = 2 * (a - b) * (a + b) := by
          rw [one_div_mul_cancel hb0.ne', one_div_mul_cancel ha0.ne']; ring
      _ = 2 := by rw [mul_assoc, hab, mul_one]
  have hk0 : 0 < k := by nlinarith
  rw [e, div_le_div_iff₀ (mul_pos hk0 ha0) hD, ← ha2]
  nlinarith [mul_le_mul_of_nonneg_left hba (sq_nonneg a),
    mul_le_mul_of_nonneg_left (mul_le_mul hba hba hb0.le ha0.le) ha0.le]

lemma tele (k : ℝ) (hk : 2 ≤ k) :
    1 / (k * Real.sqrt k) ≤ 2 * (1 / Real.sqrt (k - 1) - 1 / Real.sqrt k) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  exact inv_mul_le_two_mul_inv_sub_inv_of_sq k _ _ (Real.sqrt_pos.mpr hk0) (Real.sqrt_pos.mpr hk1) (Real.sq_sqrt hk0.le)
    (Real.sq_sqrt hk1.le)

private theorem max_div_rpow_le_two_mul_inv_sqrt_sub (c K : ℝ) (hc : 0 < c) (hK : 2 ≤ K) (hcK : c ≤ K) :
    (max 1 (K / c)) ^ (-(3 / 2 : ℝ)) ≤
      2 * c * Real.sqrt c * (1 / Real.sqrt (K - 1) - 1 / Real.sqrt K) := by
  have hKpos : 0 < K := by linarith
  have hx : 1 ≤ K / c := by rw [le_div_iff₀ hc]; linarith
  rw [max_eq_right hx, rpow_neg_three_halves (lt_of_lt_of_le one_pos hx),
    Real.sqrt_div hKpos.le c]
  have ht := tele K hK
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have e : 1 / (K / c * (Real.sqrt K / Real.sqrt c)) = c * Real.sqrt c * (1 / (K * Real.sqrt K)) := by
    rw [div_mul_div_comm, one_div_div, mul_one_div]
  rw [e]
  calc c * Real.sqrt c * (1 / (K * Real.sqrt K))
      ≤ c * Real.sqrt c * (2 * (1 / Real.sqrt (K - 1) - 1 / Real.sqrt K)) :=
        mul_le_mul_of_nonneg_left ht (mul_pos hc hsc).le
    _ = 2 * c * Real.sqrt c * (1 / Real.sqrt (K - 1) - 1 / Real.sqrt K) := by ring

lemma wt_tail (R : ℝ) (hR : 1 ≤ R) (N : ℕ) (hN : 2 * R ≤ N) (j : ℕ) :
    wt R (N + 2 + j) ≤ 2 * (2 * R) * Real.sqrt (2 * R) *
      (1 / Real.sqrt ((N : ℝ) + (j : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((j + 1 : ℕ) : ℝ))) := by
  have hc : 0 < 2 * R := by linarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have e1 : ((N + 2 + j : ℕ) : ℝ) - 1 = (N : ℝ) + ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  have e2 : (N : ℝ) + (j : ℝ) = (N : ℝ) + ((j + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  have h := max_div_rpow_le_two_mul_inv_sqrt_sub (2 * R) ((N : ℝ) + ((j + 1 : ℕ) : ℝ)) hc (by push_cast; linarith)
    (by push_cast; linarith)
  unfold wt
  rw [e1, e2]
  exact h

lemma sum_wt_le (R : ℝ) (hR : 1 ≤ R) (T : Finset ℕ) : ∑ m ∈ T, wt R m ≤ 9 * R := by
  obtain ⟨N, hN, hN'⟩ : ∃ N : ℕ, 2 * R ≤ (N : ℝ) ∧ (N : ℝ) < 2 * R + 1 :=
    ⟨⌈2 * R⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by linarith)⟩
  obtain ⟨J, hsub⟩ : ∃ J : ℕ, T ⊆ Finset.range (N + 2 + J) := by
    refine ⟨T.sup id + 1, fun m hm => ?_⟩
    have hm' : m ≤ T.sup id := Finset.le_sup (f := id) hm
    rw [Finset.mem_range]
    omega
  have h1 : ∑ m ∈ T, wt R m ≤ ∑ m ∈ Finset.range (N + 2 + J), wt R m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => wt_nonneg R m)
  rw [Finset.sum_range_add] at h1
  have h2 : ∑ m ∈ Finset.range (N + 2), wt R m ≤ (N : ℝ) + 2 := by
    calc ∑ m ∈ Finset.range (N + 2), wt R m ≤ ∑ m ∈ Finset.range (N + 2), (1 : ℝ) :=
          Finset.sum_le_sum (fun m _ => wt_le_one R m)
      _ = (N : ℝ) + 2 := by simp
  have hc : 0 < 2 * R := by linarith
  have hsc : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr hc
  have hC : 0 ≤ 2 * (2 * R) * Real.sqrt (2 * R) := (mul_pos (mul_pos two_pos hc) hsc).le
  have h3 : ∑ j ∈ Finset.range J, wt R (N + 2 + j) ≤ 4 * R := by
    calc ∑ j ∈ Finset.range J, wt R (N + 2 + j)
        ≤ ∑ j ∈ Finset.range J, 2 * (2 * R) * Real.sqrt (2 * R) *
            (1 / Real.sqrt ((N : ℝ) + (j : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((j + 1 : ℕ) : ℝ))) :=
          Finset.sum_le_sum (fun j _ => wt_tail R hR N hN j)
      _ = 2 * (2 * R) * Real.sqrt (2 * R) *
            (1 / Real.sqrt ((N : ℝ) + ((0 : ℕ) : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((J : ℕ) : ℝ))) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_range_sub' (fun j : ℕ => 1 / Real.sqrt ((N : ℝ) + (j : ℝ))) J
      _ ≤ 2 * (2 * R) * Real.sqrt (2 * R) * (1 / Real.sqrt (2 * R)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          have e0 : (N : ℝ) + ((0 : ℕ) : ℝ) = N := by simp
          rw [e0]
          have ha := one_div_le_one_div_of_le hsc (Real.sqrt_le_sqrt hN)
          have hb : 0 ≤ 1 / Real.sqrt ((N : ℝ) + ((J : ℕ) : ℝ)) := by positivity
          linarith
      _ = 4 * R := by
          rw [mul_one_div, mul_div_assoc, div_self hsc.ne', mul_one]; ring
  linarith

private theorem sum_wt_natAbs_le_nine_mul_of_injOn (R : ℝ) (hR : 1 ≤ R) (s : Finset ℤ)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, x.natAbs = y.natAbs → x = y) :
    ∑ a ∈ s, wt R a.natAbs ≤ 9 * R := by
  calc ∑ a ∈ s, wt R a.natAbs = ∑ m ∈ s.image Int.natAbs, wt R m :=
        (Finset.sum_image hinj).symm
    _ ≤ 9 * R := sum_wt_le R hR _

lemma sum_wt_int_le (R : ℝ) (hR : 1 ≤ R) (S : Finset ℤ) : ∑ a ∈ S, wt R a.natAbs ≤ 18 * R := by
  have h1 := sum_wt_natAbs_le_nine_mul_of_injOn R hR (S.filter (fun a : ℤ => 0 ≤ a)) (by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := (Finset.mem_filter.mp hx).2
    have hy0 : 0 ≤ y := (Finset.mem_filter.mp hy).2
    have ex := Int.natAbs_eq x
    have ey := Int.natAbs_eq y
    rw [hxy] at ex
    omega)
  have h2 := sum_wt_natAbs_le_nine_mul_of_injOn R hR (S.filter (fun a : ℤ => ¬ 0 ≤ a)) (by
    intro x hx y hy hxy
    have hx0 : ¬ 0 ≤ x := (Finset.mem_filter.mp hx).2
    have hy0 : ¬ 0 ≤ y := (Finset.mem_filter.mp hy).2
    have ex := Int.natAbs_eq x
    have ey := Int.natAbs_eq y
    rw [hxy] at ex
    omega)
  calc ∑ a ∈ S, wt R a.natAbs
      = ∑ a ∈ S.filter (fun a : ℤ => 0 ≤ a), wt R a.natAbs +
          ∑ a ∈ S.filter (fun a : ℤ => ¬ 0 ≤ a), wt R a.natAbs :=
        (Finset.sum_filter_add_sum_filter_not S _ _).symm
    _ ≤ 9 * R + 9 * R := add_le_add h1 h2
    _ = 18 * R := by ring

private theorem rpow_neg_three_halves_anti_of_one_le {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    t ^ (-(3 / 2 : ℝ)) ≤ s ^ (-(3 / 2 : ℝ)) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  rw [rpow_neg_three_halves hs0, rpow_neg_three_halves ht0]
  apply one_div_le_one_div_of_le (mul_pos hs0 (Real.sqrt_pos.mpr hs0))
  exact mul_le_mul hst (Real.sqrt_le_sqrt hst) (Real.sqrt_nonneg _) ht0.le

private theorem natAbs_floor_sub_one_le_abs (y : ℝ) : ((⌊y⌋.natAbs : ℕ) : ℝ) - 1 ≤ |y| := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  rcases Int.natAbs_eq ⌊y⌋ with h | h
  · have e : ((⌊y⌋ : ℤ) : ℝ) = (((⌊y⌋.natAbs : ℕ) : ℤ) : ℝ) := congrArg (fun n : ℤ => (n : ℝ)) h
    rw [Int.cast_natCast] at e
    linarith [le_abs_self y]
  · have e' : ((⌊y⌋ : ℤ) : ℝ) = -((⌊y⌋.natAbs : ℕ) : ℝ) := by exact_mod_cast h
    linarith [neg_abs_le y]

lemma floor_bound (R : ℝ) (hR : 1 ≤ R) (x : ℝ) :
    (max 1 (|x| / R)) ^ (-(3 / 2 : ℝ)) ≤ wt R (⌊2 * x⌋).natAbs := by
  have hR0 : 0 < R := by linarith
  have key : (((⌊2 * x⌋).natAbs : ℕ) : ℝ) - 1 ≤ 2 * |x| := by
    have h := natAbs_floor_sub_one_le_abs (2 * x)
    rwa [abs_mul, abs_two] at h
  unfold wt
  apply rpow_neg_three_halves_anti_of_one_le (le_max_left _ _)
  apply max_le_max le_rfl
  rw [div_le_div_iff₀ (by linarith) hR0]
  nlinarith

private theorem rpow_neg_three_le_mul_rpow_neg_three_halves {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hAC : A ≤ C) (hBC : B ≤ C) :
    C ^ (-(3 : ℝ)) ≤ A ^ (-(3 / 2 : ℝ)) * B ^ (-(3 / 2 : ℝ)) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hC0 : 0 < C := by linarith
  rw [← Real.mul_rpow hA0.le hB0.le]
  have e : C ^ (-(3 : ℝ)) = (C * C) ^ (-(3 / 2 : ℝ)) := by
    rw [Real.mul_rpow hC0.le hC0.le, ← Real.rpow_add hC0]
    norm_num
  rw [e]
  exact rpow_neg_three_halves_anti_of_one_le (by nlinarith) (mul_le_mul hAC hBC hB0.le hC0.le)

lemma cplx_bound (R : ℝ) (hR : 0 < R) (z : ℂ) :
    (max 1 (‖z‖ / R)) ^ (-(3 : ℝ)) ≤
      (max 1 (|z.re| / R)) ^ (-(3 / 2 : ℝ)) * (max 1 (|z.im| / R)) ^ (-(3 / 2 : ℝ)) := by
  have h1 : |z.re| / R ≤ ‖z‖ / R := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (inv_nonneg.mpr hR.le)
  have h2 : |z.im| / R ≤ ‖z‖ / R := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (inv_nonneg.mpr hR.le)
  exact rpow_neg_three_le_mul_rpow_neg_three_halves (le_max_left _ _) (le_max_left _ _) (max_le_max le_rfl h1)
    (max_le_max le_rfl h2)

lemma norm_lt_one_of_cell (z w : ℂ) (h1 : ⌊2 * z.re⌋ = ⌊2 * w.re⌋) (h2 : ⌊2 * z.im⌋ = ⌊2 * w.im⌋) :
    ‖z - w‖ < 1 := by
  have a1 := Int.floor_le (2 * z.re)
  have a2 := Int.lt_floor_add_one (2 * z.re)
  have b1 := Int.floor_le (2 * w.re)
  have b2 := Int.lt_floor_add_one (2 * w.re)
  have c1 := Int.floor_le (2 * z.im)
  have c2 := Int.lt_floor_add_one (2 * z.im)
  have d1 := Int.floor_le (2 * w.im)
  have d2 := Int.lt_floor_add_one (2 * w.im)
  rw [h1] at a1 a2
  rw [h2] at c1 c2
  have kre : 0 < (1 - (2 * z.re - 2 * w.re)) * (1 + (2 * z.re - 2 * w.re)) :=
    mul_pos (by linarith) (by linarith)
  have im_algebraMap_add_mul : 0 < (1 - (2 * z.im - 2 * w.im)) * (1 + (2 * z.im - 2 * w.im)) :=
    mul_pos (by linarith) (by linarith)
  have hn : ‖z - w‖ ^ 2 < 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith
  nlinarith [norm_nonneg (z - w)]

theorem latSum (ι : Type) [Fintype ι] (P : Finset (ι → ℂ)) (R : ℝ) (hR : 1 ≤ R)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 1 ≤ ∏ i, ‖p i - q i‖) :
    ∑ p ∈ P, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ)) ≤ (64 * R) ^ (2 * Fintype.card ι) := by
  classical
  have hR0 : 0 < R := by linarith
  let cell : (ι → ℂ) → (ι → ℤ × ℤ) := fun p i => (⌊2 * (p i).re⌋, ⌊2 * (p i).im⌋)
  have hf0 : ∀ x : ℤ × ℤ, 0 ≤ wt R x.1.natAbs * wt R x.2.natAbs :=
    fun x => mul_nonneg (wt_nonneg _ _) (wt_nonneg _ _)
  have hpt : ∀ p : ι → ℂ, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ)) ≤
      ∏ i, wt R (cell p i).1.natAbs * wt R (cell p i).2.natAbs := by
    intro p
    apply Finset.prod_le_prod
    · intro i _
      exact Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    · intro i _
      calc (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ))
          ≤ (max 1 (|(p i).re| / R)) ^ (-(3 / 2 : ℝ)) * (max 1 (|(p i).im| / R)) ^ (-(3 / 2 : ℝ)) :=
            cplx_bound R hR0 (p i)
        _ ≤ wt R (cell p i).1.natAbs * wt R (cell p i).2.natAbs :=
            mul_le_mul (floor_bound R hR _) (floor_bound R hR _)
              (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (wt_nonneg _ _)
  have hinj : ∀ p ∈ P, ∀ q ∈ P, cell p = cell q → p = q := by
    intro p hp q hq hpq
    by_contra hne
    have hs := hsep p hp q hq hne
    have hlt : ∀ i, ‖p i - q i‖ < 1 := by
      intro i
      have e := congrFun hpq i
      exact norm_lt_one_of_cell (p i) (q i) (congrArg Prod.fst e) (congrArg Prod.snd e)
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact hne (funext fun i => hι.elim i)
    · obtain ⟨i0⟩ := hι
      have hE : ∏ i ∈ Finset.univ.erase i0, ‖p i - q i‖ ≤ 1 :=
        Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => (hlt i).le)
      have hE0 : 0 ≤ ∏ i ∈ Finset.univ.erase i0, ‖p i - q i‖ :=
        Finset.prod_nonneg (fun i _ => norm_nonneg _)
      have hsplit : ‖p i0 - q i0‖ * ∏ i ∈ Finset.univ.erase i0, ‖p i - q i‖ = ∏ i, ‖p i - q i‖ :=
        Finset.mul_prod_erase Finset.univ (fun i => ‖p i - q i‖) (Finset.mem_univ i0)
      nlinarith [hlt i0, norm_nonneg (p i0 - q i0)]
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℤ × ℤ), ∀ c ∈ P.image cell, ∀ i, c i ∈ S :=
    ⟨(P.image cell).biUnion (fun c => Finset.univ.image c), fun c hc i =>
      Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩⟩
  have hSf : ∑ x ∈ S, wt R x.1.natAbs * wt R x.2.natAbs ≤ (18 * R) * (18 * R) := by
    calc ∑ x ∈ S, wt R x.1.natAbs * wt R x.2.natAbs
        ≤ ∑ x ∈ (S.image Prod.fst) ×ˢ (S.image Prod.snd), wt R x.1.natAbs * wt R x.2.natAbs := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
          · intro x _ _
            exact hf0 x
      _ = (∑ a ∈ S.image Prod.fst, wt R a.natAbs) * (∑ b ∈ S.image Prod.snd, wt R b.natAbs) := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ (18 * R) * (18 * R) :=
          mul_le_mul (sum_wt_int_le R hR _) (sum_wt_int_le R hR _)
            (Finset.sum_nonneg (fun b _ => wt_nonneg _ _)) (by linarith)
  calc ∑ p ∈ P, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ))
      ≤ ∑ p ∈ P, ∏ i, wt R (cell p i).1.natAbs * wt R (cell p i).2.natAbs :=
        Finset.sum_le_sum (fun p _ => hpt p)
    _ = ∑ c ∈ P.image cell, ∏ i, wt R (c i).1.natAbs * wt R (c i).2.natAbs := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ c ∈ Fintype.piFinset (fun _ : ι => S), ∏ i, wt R (c i).1.natAbs * wt R (c i).2.natAbs := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          exact Fintype.mem_piFinset.mpr (fun i => hS c hc i)
        · intro c _ _
          exact Finset.prod_nonneg (fun i _ => hf0 _)
    _ = ∏ _i : ι, ∑ x ∈ S, wt R x.1.natAbs * wt R x.2.natAbs :=
        (Finset.prod_univ_sum (fun _ : ι => S)
          (fun _ x => wt R x.1.natAbs * wt R x.2.natAbs)).symm
    _ ≤ ∏ _i : ι, ((18 * R) * (18 * R)) := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg (fun x _ => hf0 x)
        · intro i _
          exact hSf
    _ = (18 * R) ^ (2 * Fintype.card ι) := by
        rw [Finset.prod_const, Finset.card_univ, pow_mul, sq]
    _ ≤ (64 * R) ^ (2 * Fintype.card ι) := pow_le_pow_left₀ (by linarith) (by linarith) _

end Formalism.MainNotions.WeightedLatticeSum

end
