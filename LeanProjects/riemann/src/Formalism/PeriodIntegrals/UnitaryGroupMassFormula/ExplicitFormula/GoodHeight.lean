import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists

noncomputable section

namespace PI.EF

open DirichletCharacter

theorem exists_far_point (S : Finset ℝ) (a : ℝ) :
    ∃ x ∈ Set.Icc a (a + 1), ∀ y ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |x - y| := by
  by_contra hcon
  push_neg at hcon
  have hK : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have hpt : ∀ i ∈ Finset.range (S.card + 2), a + (i : ℝ) / ((S.card : ℝ) + 1) ∈ Set.Icc a (a + 1) := by
    intro i hi
    have hi' : (i : ℝ) ≤ (S.card : ℝ) + 1 := by
      have := Finset.mem_range.1 hi
      exact_mod_cast Nat.lt_succ_iff.1 this
    constructor
    · have : 0 ≤ (i : ℝ) / ((S.card : ℝ) + 1) := by positivity
      linarith
    · have : (i : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := (div_le_one hK).2 hi'
      linarith
  have hex : ∀ i ∈ Finset.range (S.card + 2), ∃ y ∈ S,
      |a + (i : ℝ) / ((S.card : ℝ) + 1) - y| < 1 / (2 * ((S.card : ℝ) + 1)) :=
    fun i hi => hcon _ (hpt i hi)
  choose! g hgS hgd using hex
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (S.card + 2)) (t := S) (by simp) (fun i hi => hgS i hi)
  have h1 := hgd i hi
  have h2 := hgd j hj
  rw [heq] at h1
  have hlt : |(a + (i : ℝ) / ((S.card : ℝ) + 1)) - (a + (j : ℝ) / ((S.card : ℝ) + 1))| <
      1 / ((S.card : ℝ) + 1) := by
    have htri := abs_sub_le (a + (i : ℝ) / ((S.card : ℝ) + 1)) (g j) (a + (j : ℝ) / ((S.card : ℝ) + 1))
    rw [abs_sub_comm (g j)] at htri
    have e : 1 / (2 * ((S.card : ℝ) + 1)) + 1 / (2 * ((S.card : ℝ) + 1)) = 1 / ((S.card : ℝ) + 1) := by
      field_simp
      ring
    linarith
  have hge : 1 / ((S.card : ℝ) + 1) ≤
      |(a + (i : ℝ) / ((S.card : ℝ) + 1)) - (a + (j : ℝ) / ((S.card : ℝ) + 1))| := by
    rw [show (a + (i : ℝ) / ((S.card : ℝ) + 1)) - (a + (j : ℝ) / ((S.card : ℝ) + 1)) =
      ((i : ℝ) - j) / ((S.card : ℝ) + 1) by ring, abs_div, abs_of_pos hK]
    apply div_le_div_of_nonneg_right _ hK.le
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      exact le_abs.2 (Or.inr (by linarith))
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      exact le_abs.2 (Or.inl (by linarith))
  linarith

theorem analyticOnNhd_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    AnalyticOnNhd ℂ (LFunction χ) {(1 : ℂ)}ᶜ := by
  exact DifferentiableOn.analyticOnNhd
    (fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt)
    isOpen_compl_singleton

theorem analyticAt_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (LFunction χ) s := by
  exact analyticOnNhd_LFunction χ s hs

theorem analyticOrderAt_LFunction_ne_top {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s ≠ 1) : analyticOrderAt (LFunction χ) s ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have hz := (analyticOnNhd_LFunction χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hs htop
  have h2 := hz (show (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) by norm_num)
  exact LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num) h2

theorem one_le_mult {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s ≠ 1) (h0 : LFunction χ s = 0) : 1 ≤ analyticOrderNatAt (LFunction χ) s := by
  have hne := analyticOrderAt_LFunction_ne_top χ hs
  have h0' : analyticOrderAt (LFunction χ) s ≠ 0 := by
    rw [Ne, (analyticAt_LFunction χ hs).analyticOrderAt_eq_zero]
    exact not_not.2 h0
  have hn : analyticOrderNatAt (LFunction χ) s ≠ 0 := by
    intro h
    apply h0'
    rw [← Nat.cast_analyticOrderNatAt hne, h]
    rfl
  omega

def wsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ ZerosNear χ t, (mult χ ρ : ℝ)

theorem ne_one_of_re_lt {ρ : ℂ} (h : ρ.re < 1) : ρ ≠ 1 := by
  rintro rfl
  simp at h

theorem wsum_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T t : ℝ} (_hT : 0 ≤ T) (ht : |t| ≤ T + 1) :
    wsum χ t ≤ C * Real.log (N * (T + 3)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold wsum
  refine le_trans (hC N χ hχ t).2 ?_
  apply mul_le_mul_of_nonneg_left _ hC0
  apply Real.log_le_log (by positivity)
  apply mul_le_mul_of_nonneg_left _ hNpos.le
  linarith

theorem sum_mult_le_of_subset {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {t1 t2 : ℝ}
    (h1 : (ZerosNear χ t1).Finite) (h2 : (ZerosNear χ t2).Finite) (B : Finset ℂ)
    (hB : (B : Set ℂ) ⊆ ZerosNear χ t1 ∪ ZerosNear χ t2) :
    ∑ ρ ∈ B, (mult χ ρ : ℝ) ≤ wsum χ t1 + wsum χ t2 := by
  classical
  unfold wsum
  rw [finsum_mem_eq_finite_toFinset_sum _ h1, finsum_mem_eq_finite_toFinset_sum _ h2]
  have hsub : B ⊆ h1.toFinset ∪ h2.toFinset := by
    intro x hx
    have := hB (Finset.mem_coe.2 hx)
    simp only [Finset.mem_union, Set.Finite.mem_toFinset]
    exact this
  calc ∑ ρ ∈ B, (mult χ ρ : ℝ) ≤ ∑ ρ ∈ h1.toFinset ∪ h2.toFinset, (mult χ ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_union_inter]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

theorem card_le_sum_mult {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (B : Finset ℂ)
    (hB : ∀ ρ ∈ B, ρ.re < 1 ∧ LFunction χ ρ = 0) :
    (B.card : ℝ) ≤ ∑ ρ ∈ B, (mult χ ρ : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  obtain ⟨h1, h0⟩ := hB ρ hρ
  exact_mod_cast one_le_mult χ (ne_one_of_re_lt h1) h0

theorem zerosBelow_finite {C : ℝ} (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (T : ℝ) : (ZerosBelow χ T).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.Icc (-⌈T⌉) ⌈T⌉).finite_toSet
    (fun n _ => (hC N χ hχ (n : ℝ)).1)) ?_
  intro ρ hρ
  obtain ⟨h0, h1, him, hL⟩ := hρ
  have hb := abs_lt.1 him
  refine Set.mem_biUnion (x := ⌊ρ.im⌋) (Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨?_, ?_⟩))
    ⟨h0, h1, ?_, hL⟩
  · have h := Int.floor_mono hb.1.le
    rw [Int.floor_neg] at h
    exact h
  · exact (Int.floor_mono hb.2.le).trans (Int.floor_le_ceil T)
  · rw [abs_le]
    constructor <;> linarith [Int.floor_le ρ.im, Int.sub_one_lt_floor ρ.im]

theorem mem_window_of_abs {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {ρ : ℂ} {t : ℝ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hL : LFunction χ ρ = 0) (h : |(|ρ.im|) - t| ≤ 1) :
    ρ ∈ ZerosNear χ t ∪ ZerosNear χ (-t) := by
  rcases le_or_gt 0 ρ.im with hi | hi
  · left
    refine ⟨h0, h1, ?_, hL⟩
    rwa [abs_of_nonneg hi] at h
  · right
    refine ⟨h0, h1, ?_, hL⟩
    rw [abs_of_neg hi] at h
    rw [show ρ.im - -t = -(-ρ.im - t) by ring, abs_neg]
    exact h

theorem exists_good_height {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    ∃ T' ∈ Set.Icc T (T + 1), ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → LFunction χ ρ = 0 →
      1 / (2 * (2 * C * Real.log (N * (T + 3)) + 1)) ≤ |(|ρ.im|) - T'| := by
  have hf1 := (hC N χ hχ (T + 1 / 2)).1
  have hf2 := (hC N χ hχ (-(T + 1 / 2))).1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hlog : 0 ≤ Real.log (N * (T + 3)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hN1 (by linarith))
  have hK0 : 0 ≤ 2 * C * Real.log (N * (T + 3)) := mul_nonneg (mul_nonneg (by norm_num) hC0) hlog
  have hcardS : (((hf1.union hf2).toFinset.image (fun ρ : ℂ => |ρ.im|)).card : ℝ) ≤
      2 * C * Real.log (N * (T + 3)) := by
    calc (((hf1.union hf2).toFinset.image (fun ρ : ℂ => |ρ.im|)).card : ℝ)
        ≤ ((hf1.union hf2).toFinset.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ ∑ ρ ∈ (hf1.union hf2).toFinset, (mult χ ρ : ℝ) :=
          card_le_sum_mult χ _ (fun ρ hρ => by
            rw [Set.Finite.mem_toFinset] at hρ
            rcases hρ with h | h
            · exact ⟨h.2.1, h.2.2.2⟩
            · exact ⟨h.2.1, h.2.2.2⟩)
      _ ≤ wsum χ (T + 1 / 2) + wsum χ (-(T + 1 / 2)) :=
          sum_mult_le_of_subset χ hf1 hf2 _ (by
            intro x hx
            simpa using hx)
      _ ≤ C * Real.log (N * (T + 3)) + C * Real.log (N * (T + 3)) :=
          add_le_add
            (wsum_le hC0 hC χ hχ hT (by rw [abs_of_nonneg (by linarith)]; linarith))
            (wsum_le hC0 hC χ hχ hT (by rw [abs_neg, abs_of_nonneg (by linarith)]; linarith))
      _ = 2 * C * Real.log (N * (T + 3)) := by ring
  obtain ⟨x, hx, hfar⟩ := exists_far_point ((hf1.union hf2).toFinset.image (fun ρ : ℂ => |ρ.im|)) T
  refine ⟨x, hx, fun ρ h0 h1 hL => ?_⟩
  have hmono : 1 / (2 * (2 * C * Real.log (N * (T + 3)) + 1)) ≤
      1 / (2 * ((((hf1.union hf2).toFinset.image (fun ρ : ℂ => |ρ.im|)).card : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  by_cases hw : |(|ρ.im|) - (T + 1 / 2)| ≤ 1
  · have hρB : ρ ∈ (hf1.union hf2).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact mem_window_of_abs χ h0 h1 hL hw
    have h3 := hfar (|ρ.im|) (Finset.mem_image_of_mem _ hρB)
    rw [abs_sub_comm] at h3
    linarith
  · push_neg at hw
    have hx' : |x - (T + 1 / 2)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have htri := abs_sub_le (|ρ.im|) x (T + 1 / 2)
    have h3 : 1 / (2 * (2 * C * Real.log (N * (T + 3)) + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith

theorem trunc_change {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T T' u : ℝ} (hT : 0 < T)
    (hT' : T' ∈ Set.Icc T (T + 1)) (hu : 1 ≤ u) :
    ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
        ∑ᶠ ρ ∈ ZerosBelow χ T, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
      2 * C * Real.log (N * (T + 3)) * (u / T) := by
  classical
  have hF' := zerosBelow_finite hC χ hχ T'
  have hF := zerosBelow_finite hC χ hχ T
  rw [finsum_mem_eq_finite_toFinset_sum _ hF', finsum_mem_eq_finite_toFinset_sum _ hF]
  have hsub : hF.toFinset ⊆ hF'.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨a, b, c, d⟩ := hρ
    exact ⟨a, b, lt_of_lt_of_le c hT'.1, d⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hD : ∀ ρ ∈ hF'.toFinset \ hF.toFinset, 0 < ρ.re ∧ ρ.re < 1 ∧ T ≤ |ρ.im| ∧
      |ρ.im| ≤ T + 1 ∧ LFunction χ ρ = 0 := by
    intro ρ hρ
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hρ
    obtain ⟨⟨a, b, c, d⟩, hn⟩ := hρ
    refine ⟨a, b, ?_, by linarith [hT'.2], d⟩
    by_contra hlt
    push_neg at hlt
    exact hn ⟨a, b, hlt, d⟩
  have hsumm : ∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℝ) ≤
      2 * C * Real.log (N * (T + 3)) := by
    have hf1 := (hC N χ hχ (T + 1 / 2)).1
    have hf2 := (hC N χ hχ (-(T + 1 / 2))).1
    calc ∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℝ)
        ≤ wsum χ (T + 1 / 2) + wsum χ (-(T + 1 / 2)) :=
          sum_mult_le_of_subset χ hf1 hf2 _ (fun ρ hρ => by
            obtain ⟨a, b, c, d, e⟩ := hD ρ hρ
            exact mem_window_of_abs χ a b e (by rw [abs_le]; constructor <;> linarith))
      _ ≤ C * Real.log (N * (T + 3)) + C * Real.log (N * (T + 3)) :=
          add_le_add
            (wsum_le hC0 hC χ hχ hT.le (by rw [abs_of_pos (by linarith)]; linarith))
            (wsum_le hC0 hC χ hχ hT.le (by rw [abs_neg, abs_of_pos (by linarith)]; linarith))
      _ = 2 * C * Real.log (N * (T + 3)) := by ring
  have hu0 : (0 : ℝ) < u := by linarith
  have hterm : ∀ ρ ∈ hF'.toFinset \ hF.toFinset,
      ‖(mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (mult χ ρ : ℝ) * (u / T) := by
    intro ρ hρ
    obtain ⟨a, b, c, d, e⟩ := hD ρ hρ
    have hρn : T ≤ ‖ρ‖ := c.trans (Complex.abs_im_le_norm ρ)
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply div_le_div₀ hu0.le _ hT hρn
    calc u ^ ρ.re ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu b.le
      _ = u := Real.rpow_one u
  calc ‖∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖
      ≤ ∑ ρ ∈ hF'.toFinset \ hF.toFinset, ‖(mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℝ) * (u / T) := Finset.sum_le_sum hterm
    _ = (∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℝ)) * (u / T) := by rw [Finset.sum_mul]
    _ ≤ 2 * C * Real.log (N * (T + 3)) * (u / T) :=
        mul_le_mul_of_nonneg_right hsumm (div_nonneg hu0.le hT.le)

theorem four_mul_le_cube {x : ℝ} (hx : 2 ≤ x) : 4 * x ≤ x ^ 3 := by
  have h4 : 4 ≤ x ^ 2 := by nlinarith
  nlinarith

theorem goodHeightExists_of {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) :
    GoodHeightExists (12 * C + 4) := by
  intro N _ χ hχ T hT
  obtain ⟨T', hT', hgood⟩ := exists_good_height hC0 hC χ hχ (by linarith : (0 : ℝ) ≤ T)
  refine ⟨T', hT'.1, hT'.2, fun ρ h0 h1 hL => le_trans ?_ (hgood ρ h0 h1 hL)⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hT2 : 2 ≤ T' := le_trans hT hT'.1
  have hNT : 2 ≤ (N : ℝ) * T' := by nlinarith
  have hL' : 1 / 2 ≤ Real.log (N * T') := by
    have := Real.log_le_log (by norm_num) hNT
    linarith [Real.log_two_gt_d9]
  have hpos3 : (0 : ℝ) < N * (T + 3) := mul_pos (by linarith) (by linarith)
  have hL : Real.log (N * (T + 3)) ≤ 3 * Real.log (N * T') := by
    have hle : (N : ℝ) * (T + 3) ≤ (N * T') ^ 3 := by
      have h4 := four_mul_le_cube hT2
      have hN3 : (N : ℝ) ≤ N ^ 3 := le_self_pow₀ hN1 (by norm_num)
      calc (N : ℝ) * (T + 3) ≤ N * (4 * T') :=
            mul_le_mul_of_nonneg_left (by linarith [hT'.1]) (by linarith)
        _ ≤ N * T' ^ 3 := mul_le_mul_of_nonneg_left h4 (by linarith)
        _ ≤ N ^ 3 * T' ^ 3 := mul_le_mul_of_nonneg_right hN3 (by positivity)
        _ = (N * T') ^ 3 := by ring
    calc Real.log (N * (T + 3)) ≤ Real.log ((N * T') ^ 3) := Real.log_le_log hpos3 hle
      _ = 3 * Real.log (N * T') := by rw [Real.log_pow]; norm_num
  have hlogpos : 0 ≤ Real.log (N * (T + 3)) := Real.log_nonneg (by nlinarith)
  have hCL := mul_nonneg hC0 hlogpos
  have h1 : C * Real.log (N * (T + 3)) ≤ C * (3 * Real.log (N * T')) :=
    mul_le_mul_of_nonneg_left hL hC0
  apply one_div_le_one_div_of_le (by nlinarith)
  nlinarith

theorem truncChange_of {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) : TruncChange (4 * C) := by
  intro N _ χ hχ u T T' hT hTu hTT' hT'
  have hmain := trunc_change hC0 hC χ hχ (by linarith : (0 : ℝ) < T) ⟨hTT', hT'⟩
    (by linarith : (1 : ℝ) ≤ u)
  unfold zsum
  refine le_trans hmain ?_
  unfold Err
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hT0 : 0 < T := by linarith
  have huT4 : (4 : ℝ) ≤ u * T := by nlinarith
  have hNuT : 4 ≤ (N : ℝ) * u * T := by
    have h := mul_le_mul_of_nonneg_right hN1 (by linarith : (0 : ℝ) ≤ u * T)
    have e : (N : ℝ) * u * T = N * (u * T) := by ring
    rw [e]
    linarith
  have hL2 : 1 ≤ Real.log (N * u * T) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hLle : Real.log (N * (T + 3)) ≤ 2 * Real.log (N * u * T) := by
    have hT2 : 4 ≤ T ^ 2 := by nlinarith
    have hA : T + 3 ≤ T ^ 2 * T ^ 2 := by nlinarith
    have hB : T ^ 2 ≤ u ^ 2 := by nlinarith
    have hC' : (N : ℝ) ≤ N ^ 2 := by nlinarith
    have hle : (N : ℝ) * (T + 3) ≤ (N * u * T) ^ 2 := by
      calc (N : ℝ) * (T + 3) ≤ N * (T ^ 2 * T ^ 2) := mul_le_mul_of_nonneg_left hA (by linarith)
        _ ≤ N ^ 2 * (u ^ 2 * T ^ 2) :=
            mul_le_mul hC' (mul_le_mul_of_nonneg_right hB (by positivity)) (by positivity)
              (by positivity)
        _ = (N * u * T) ^ 2 := by ring
    calc Real.log (N * (T + 3)) ≤ Real.log ((N * u * T) ^ 2) :=
          Real.log_le_log (mul_pos (by linarith) (by linarith)) hle
      _ = 2 * Real.log (N * u * T) := by rw [Real.log_pow]; norm_num
  have hlogNu : 0 ≤ Real.log (N * u) := Real.log_nonneg (by nlinarith)
  have huT : 0 ≤ u / T := div_nonneg (by linarith) hT0.le
  have h1 : Real.log (N * (T + 3)) ≤ 2 * Real.log (N * u * T) ^ 2 := by nlinarith
  have h2 : 2 * C * Real.log (N * (T + 3)) * (u / T) ≤
      4 * C * (u * Real.log (N * u * T) ^ 2 / T) := by
    have e : u * Real.log (N * u * T) ^ 2 / T = Real.log (N * u * T) ^ 2 * (u / T) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC0) huT)
    nlinarith
  have h3 : 4 * C * (u * Real.log (N * u * T) ^ 2 / T) ≤
      4 * C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u)) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hlogNu) (by linarith)
  linarith

end PI.EF
