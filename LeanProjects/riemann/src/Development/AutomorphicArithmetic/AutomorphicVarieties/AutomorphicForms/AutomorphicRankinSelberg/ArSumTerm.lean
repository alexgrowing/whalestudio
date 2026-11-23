import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open scoped ComplexConjugate

private lemma arSum_term (r : ℕ) (t : ℝ) (ht : (r : ℝ) + 1 ≤ t) (x y : ℝ) (n₁ m : ℕ) (hx : 0 ≤ x)
    (hn : 1 ≤ n₁ * m ^ 2) (h : x ≤ y * (m : ℝ) ^ r) :
    x ^ 2 / ((n₁ * m ^ 2 : ℕ) : ℝ) ^ t ≤ y ^ 2 / (n₁ : ℝ) ^ t * (1 / (m : ℝ) ^ 2) := by
  have hn1 : 1 ≤ n₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hn1r : (1:ℝ) ≤ n₁ := by exact_mod_cast hn1
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx2 : x ^ 2 ≤ y ^ 2 * ((m:ℝ) ^ r) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx h 2
  have hM : (m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2 ≤ ((m:ℝ) ^ 2) ^ t := by
    have h1 : ((m:ℝ) ^ 2) ^ (r + 1) = (m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2 := by ring
    rw [← h1, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by push_cast; linarith)
  have hcast : ((n₁ * m ^ 2 : ℕ) : ℝ) ^ t = (n₁ : ℝ) ^ t * ((m:ℝ) ^ 2) ^ t := by
    push_cast
    exact Real.mul_rpow (by positivity) (by positivity)
  have hN : (0:ℝ) < (n₁ : ℝ) ^ t := Real.rpow_pos_of_pos (by linarith) t
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  rw [hcast]
  calc x ^ 2 / ((n₁ : ℝ) ^ t * ((m:ℝ) ^ 2) ^ t)
      ≤ (y ^ 2 * ((m:ℝ) ^ r) ^ 2) / ((n₁ : ℝ) ^ t * ((m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2)) :=
        div_le_div₀ (by positivity) hx2 (by positivity) (mul_le_mul_of_nonneg_left hM hN.le)
    _ = y ^ 2 / (n₁ : ℝ) ^ t * (1 / (m:ℝ) ^ 2) := by
        field_simp

theorem UpperTheory.V.Af.Rs.arSum :
    UpperTheory.V.Af.Rs.ArSum := by
  intro r t a b P ht hP h3 hsu
  have ht0 : 0 < t := by have : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith
  set u : ℕ → ℝ := fun n => ‖a n‖ ^ 2 / (n:ℝ) ^ t with hu
  set w : ℕ → ℂ := fun n => starRingEnd ℂ (b n) * a n / (((n:ℝ) ^ t : ℝ) : ℂ) with hw
  have h3' : ∀ n : ℕ, ∃ q : ℕ × ℕ, 1 ≤ n → a n ≠ 0 →
      q.1 ∈ P ∧ n = q.1 * q.2 ^ 2 ∧ ‖a n‖ ≤ ‖a q.1‖ * (q.2:ℝ) ^ r ∧ ‖b n‖ ≤ ‖a q.1‖ * (q.2:ℝ) ^ r := by
    intro n
    by_cases hc : 1 ≤ n ∧ a n ≠ 0
    · obtain ⟨n₁, hn₁, m, h1, h2, h4⟩ := h3 n hc.1 hc.2
      exact ⟨(n₁, m), fun _ _ => ⟨hn₁, h1, h2, h4⟩⟩
    · exact ⟨(0, 0), fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose φ hφ using h3'
  set Q : Set ℕ := {n | n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0} with hQ
  set c : ℕ → ℝ := ({m | 2 ≤ m} : Set ℕ).indicator (fun m => 1 / (m:ℝ) ^ 2) with hc
  set g : ℕ × ℕ → ℝ := fun q => P.indicator u q.1 * c q.2 with hg
  set G : ℕ → ℝ := Q.indicator (fun n => g (φ n)) with hG
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hu]; positivity
  have hc0 : ∀ m, 0 ≤ c m := fun m => by
    simp only [hc]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _
  have hPu : Summable (P.indicator u) := hsu.indicator P
  have hzeta : Summable (fun m : ℕ => 1 / (m:ℝ) ^ 2) := hasSum_zeta_two.summable
  have hcs : Summable c := hzeta.indicator _
  have hgs : Summable g :=
    summable_mul_of_summable_norm (f := P.indicator u) (g := c)
      (summable_norm_iff.mpr hPu) (summable_norm_iff.mpr hcs)
  have hg0 : ∀ q, 0 ≤ g q := fun q =>
    mul_nonneg (Set.indicator_nonneg (fun n _ => hu0 n) _) (hc0 _)
  have hinj : Function.Injective (fun x : Q => φ x.1) := by
    intro x y hxy
    have hxQ : x.1 ∉ P ∧ 1 ≤ x.1 ∧ a x.1 ≠ 0 := x.2
    have hyQ : y.1 ∉ P ∧ 1 ≤ y.1 ∧ a y.1 ≠ 0 := y.2
    have hx := hφ x.1 hxQ.2.1 hxQ.2.2
    have hy := hφ y.1 hyQ.2.1 hyQ.2.2
    apply Subtype.ext
    simp only at hxy
    rw [hx.2.1, hy.2.1, hxy]
  have hGs : Summable G := by
    rw [hG, ← summable_subtype_iff_indicator]
    exact hgs.comp_injective hinj
  have hc34 : ∑' m, c m ≤ 3 / 4 := by
    have e1 := hzeta.sum_add_tsum_nat_add 2
    have e2 := hcs.sum_add_tsum_nat_add 2
    have s2 : ∑ i ∈ Finset.range 2, c i = 0 := by simp [Finset.sum_range_succ, hc]
    have s1 : ∑ i ∈ Finset.range 2, (1 / ((i:ℕ):ℝ) ^ 2) = 1 := by simp [Finset.sum_range_succ]
    have e3 : (fun i => c (i + 2)) = (fun i => 1 / (((i + 2 : ℕ)) : ℝ) ^ 2) := by
      funext i
      simp only [hc]
      rw [Set.indicator_of_mem (show i + 2 ∈ {m : ℕ | 2 ≤ m} by simp)]
    rw [s2, zero_add, e3] at e2
    rw [s1, hasSum_zeta_two.tsum_eq] at e1
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have hpi2 : Real.pi ^ 2 < 9.93 := by nlinarith
    rw [← e2]
    linarith
  have hGle : ∑' n, G n ≤ (∑' n, P.indicator u n) * (3 / 4) := by
    rw [hG, ← tsum_subtype]
    calc ∑' x : Q, g (φ x) ≤ ∑' q, g q := tsum_comp_le_tsum_of_inj hgs hg0 hinj
      _ = (∑' n, P.indicator u n) * ∑' m, c m := by
          exact (tsum_mul_tsum_of_summable_norm (f := P.indicator u) (g := c)
            (summable_norm_iff.mpr hPu) (summable_norm_iff.mpr hcs)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hc34
          (tsum_nonneg (fun n => Set.indicator_nonneg (fun n _ => hu0 n) _))
  have hpt : ∀ n, ‖w n‖ ≤ P.indicator u n + G n ∧
      6 * P.indicator u n - 8 * G n ≤ 7 * (w n).re - u n := by
    intro n
    by_cases hn : n ∈ P
    · have hGn : G n = 0 := by
        simp only [hG]
        have hnQ : n ∉ Q := fun h => by
          have h' : n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0 := h
          exact h'.1 hn
        exact Set.indicator_of_notMem hnQ _
      have hPn : P.indicator u n = u n := Set.indicator_of_mem hn u
      have hwn : w n = ((u n : ℝ) : ℂ) := by
        simp only [hw, hu]
        rw [hP n hn, Complex.conj_mul']
        push_cast
        ring
      rw [hGn, hPn, hwn, Complex.norm_real, Real.norm_of_nonneg (hu0 n), Complex.ofReal_re]
      constructor <;> linarith [hu0 n]
    · have hPn : P.indicator u n = 0 := Set.indicator_of_notMem hn u
      by_cases hq : 1 ≤ n ∧ a n ≠ 0
      · have hφn := hφ n hq.1 hq.2
        have hGn : G n = P.indicator u (φ n).1 * c (φ n).2 := by
          simp only [hG, hg]
          exact Set.indicator_of_mem (show n ∈ Q from ⟨hn, hq.1, hq.2⟩) _
        rcases hφq : φ n with ⟨n₁, m⟩
        rw [hφq] at hφn hGn
        obtain ⟨hn₁P, hnm, hA, hB⟩ := hφn
        simp only at hn₁P hnm hA hB hGn
        rcases Nat.lt_or_ge m 2 with hlt | hm2
        · exfalso
          interval_cases m
          · simp at hnm
            omega
          · simp at hnm
            exact hn (hnm ▸ hn₁P)
        have hc2 : c m = 1 / (m:ℝ) ^ 2 := by
          simp only [hc]
          exact Set.indicator_of_mem (show m ∈ {m : ℕ | 2 ≤ m} from hm2) _
        have hPn1 : P.indicator u n₁ = u n₁ := Set.indicator_of_mem hn₁P u
        rw [hc2, hPn1] at hGn
        have h1n : 1 ≤ n₁ * m ^ 2 := hnm ▸ hq.1
        have k1 := arSum_term r t ht ‖a n‖ ‖a n₁‖ n₁ m (norm_nonneg _) h1n hA
        have k2 := arSum_term r t ht ‖b n‖ ‖a n₁‖ n₁ m (norm_nonneg _) h1n hB
        rw [← hnm] at k1 k2
        have hnt : 0 < (n:ℝ) ^ t := Real.rpow_pos_of_pos (by exact_mod_cast hq.1) t
        have hwn : ‖w n‖ = ‖b n‖ * ‖a n‖ / (n:ℝ) ^ t := by
          simp only [hw]
          rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hnt.le]
        have hw2 : ‖w n‖ ≤ G n := by
          rw [hwn, hGn]
          have hab : ‖b n‖ * ‖a n‖ ≤ (‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]
          calc ‖b n‖ * ‖a n‖ / (n:ℝ) ^ t ≤ ((‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2) / (n:ℝ) ^ t := by gcongr
            _ = (‖a n‖ ^ 2 / (n:ℝ) ^ t + ‖b n‖ ^ 2 / (n:ℝ) ^ t) / 2 := by ring
            _ ≤ _ := by simp only [hu]; linarith
        have hun : u n ≤ G n := by
          rw [hGn]
          simp only [hu]
          exact k1
        have hre : -‖w n‖ ≤ (w n).re := by
          have := Complex.abs_re_le_norm (w n)
          linarith [neg_abs_le (w n).re]
        rw [hPn]
        constructor <;> linarith
      · have hGn : G n = 0 := by
          simp only [hG]
          have hnQ : n ∉ Q := fun h => by
            have h' : n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0 := h
            exact hq ⟨h'.2.1, h'.2.2⟩
          exact Set.indicator_of_notMem hnQ _
        have hz : w n = 0 ∧ u n = 0 := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            simp [hw, hu, Real.zero_rpow (ne_of_gt ht0)]
          · have han : a n = 0 := by
              by_contra h
              exact hq ⟨h0, h⟩
            simp [hw, hu, han]
        rw [hPn, hGn, hz.1, hz.2]
        simp
  have hws : Summable w := Summable.of_norm_bounded (hPu.add hGs) (fun n => (hpt n).1)
  have hres : Summable (fun n => (w n).re) :=
    Summable.of_norm_bounded (hPu.add hGs)
      (fun n => by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hpt n).1)
  rw [Complex.re_tsum hws]
  have hD := Summable.tsum_le_tsum (fun n => (hpt n).2)
    ((hPu.mul_left 6).sub (hGs.mul_left 8)) ((hres.mul_left 7).sub hsu)
  rw [Summable.tsum_sub (hPu.mul_left 6) (hGs.mul_left 8),
    Summable.tsum_sub (hres.mul_left 7) hsu, Summable.tsum_mul_left 6 hPu,
    Summable.tsum_mul_left 8 hGs, Summable.tsum_mul_left 7 hres] at hD
  linarith [hGle]
