import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
open PowerSeries GlobalTheory.Honda

noncomputable section

namespace GlobalTheory.Honda.HeightTwo

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_natCast_coprime_eq_one (l u : ℕ) (hp : l.Prime) (hl1 : ‖(l : K)‖ < 1) (hu : ¬ l ∣ u) :
    ‖(u : K)‖ = 1 := by
  have hcop : Nat.Coprime u l := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K u) (not_lt.mp fun h => ?_)
  have hb := Nat.gcd_eq_gcd_ab u l
  rw [hcop.gcd_eq_one] at hb
  have hK := congrArg (fun z : ℤ => (z : K)) hb
  push_cast at hK
  have h1 : ‖(u : K) * (Nat.gcdA u l : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(u : K)‖ * ‖(Nat.gcdA u l : K)‖ ≤ ‖(u : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one K _) (norm_nonneg _)
      _ < 1 := by simpa using h
  have h2 : ‖(l : K) * (Nat.gcdB u l : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖(Nat.gcdB u l : K)‖ ≤ ‖(l : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one K _) (norm_nonneg _)
      _ < 1 := by simpa using hl1
  have h3 := IsUltrametricDist.norm_add_le_max ((u : K) * (Nat.gcdA u l : K)) ((l : K) * (Nat.gcdB u l : K))
  rw [← hK, norm_one] at h3
  exact absurd h3 (not_le.mpr (max_lt h1 h2))

theorem pow_le_norm_natCast (l : ℕ) (hp : l.Prime) (hl1 : ‖(l : K)‖ < 1) (k : ℕ) (hk : 1 ≤ k) :
    ‖(l : K)‖ ^ (k - 1) ≤ ‖(k : K)‖ := by
  obtain ⟨v, u, hu, hkv⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : k ≠ 0) l hp.one_lt.ne'
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero l)
  have hvk : v ≤ k - 1 := by
    have h1 : v < l ^ v := Nat.lt_pow_self hp.one_lt
    have h2 : l ^ v ≤ k := by rw [hkv]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
    omega
  have hn : ‖(k : K)‖ = ‖(l : K)‖ ^ v := by
    rw [hkv]; push_cast
    rw [norm_mul, norm_pow, norm_natCast_coprime_eq_one l u hp hl1 hu, mul_one]
  rw [hn]
  exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le hvk

theorem coeff_mul_pow_le (l : ℕ) (hp : l.Prime) (hl1 : ‖(l : K)‖ < 1) (f : K⟦X⟧)
    (hder : CoefLe 1 (derivative K f)) (k : ℕ) (hk : 1 ≤ k) :
    ‖coeff k f‖ * ‖(l : K)‖ ^ k ≤ ‖(l : K)‖ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hd := hder k'
  rw [coeff_derivative, norm_mul] at hd
  have hle := pow_le_norm_natCast l hp hl1 (k' + 1) hk
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hle
  calc ‖coeff (k' + 1) f‖ * ‖(l : K)‖ ^ (k' + 1)
      = (‖coeff (k' + 1) f‖ * ‖(l : K)‖ ^ k') * ‖(l : K)‖ := by ring
    _ ≤ 1 * ‖(l : K)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (mul_le_mul_of_nonneg_left hle (norm_nonneg _)).trans hd
    _ = ‖(l : K)‖ := one_mul _

theorem norm_coeff_pow_le (g : K⟦X⟧) (r : ℝ) (m : ℕ) (hr : 0 ≤ r) (hg : ∀ j ≤ m, ‖coeff j g‖ ≤ r) :
    ∀ k j, j ≤ m → ‖coeff j (g ^ k)‖ ≤ r ^ k := by
  intro k
  induction k with
  | zero =>
    intro j _
    rw [pow_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    intro j hj
    rw [pow_succ', coeff_mul, pow_succ']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [norm_mul]
    exact mul_le_mul (hg _ (by omega)) (ih _ (by omega)) (norm_nonneg _) hr

theorem norm_coeff_succ_pow_le (g : K⟦X⟧) (hg0 : constantCoeff g = 0) (r : ℝ) (m : ℕ) (hr : 0 ≤ r)
    (hg : ∀ j ≤ m, ‖coeff j g‖ ≤ r) (k : ℕ) :
    ‖coeff (m + 1) (g ^ (k + 2))‖ ≤ r ^ (k + 2) := by
  rw [pow_succ' g (k + 1), coeff_mul, pow_succ' r (k + 1)]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases ha : p.1 = 0
  · rw [ha, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, norm_zero]; positivity
  by_cases hb : p.2 = 0
  · rw [hb, coeff_zero_eq_constantCoeff_apply, map_pow, hg0, zero_pow (by omega), mul_zero, norm_zero]
    positivity
  rw [norm_mul]
  exact mul_le_mul (hg _ (by omega)) (norm_coeff_pow_le g r m hr hg _ _ (by omega)) (norm_nonneg _) hr

theorem coeff_subst_eq_sum (f g : K⟦X⟧) (hg0 : constantCoeff g = 0) (n : ℕ) :
    coeff n (subst g f) = ∑ d ∈ Finset.range (n + 1), coeff d f * coeff n (g ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg0)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hdn
    apply hd
    obtain ⟨g', rfl⟩ := X_dvd_iff.mpr hg0
    simp only [mul_pow, coeff_X_pow_mul', if_neg (by omega : ¬ d ≤ n), smul_zero]

theorem norm_coeff_le_of_subst (f g : K⟦X⟧) (ρ : ℝ) (hρ : 0 ≤ ρ) (hf0 : coeff 0 f = 0) (hf1 : coeff 1 f = 1)
    (hf : ∀ k, 1 ≤ k → ‖coeff k f‖ * ρ ^ k ≤ ρ) (hg0 : constantCoeff g = 0) (N : ℕ)
    (hy : ∀ n ≤ N, ‖coeff n (subst g f)‖ ≤ ρ) : ∀ n ≤ N, ‖coeff n g‖ ≤ ρ := by
  have key : ∀ m, m ≤ N → ∀ j ≤ m, ‖coeff j g‖ ≤ ρ := by
    intro m
    induction m with
    | zero =>
      intro _ j hj
      rw [Nat.le_zero.mp hj, coeff_zero_eq_constantCoeff_apply, hg0, norm_zero]; exact hρ
    | succ m ih =>
      intro hm j hj
      rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
      · exact ih (by omega) j (by omega)
      obtain rfl : j = m + 1 := by omega
      have ih' := ih (by omega)
      have hs := coeff_subst_eq_sum f g hg0 (m + 1)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : 1 < m + 1 + 1)), hf1, pow_one,
        one_mul] at hs
      have hrest : ‖∑ d ∈ (Finset.range (m + 1 + 1)).erase 1, coeff d f * coeff (m + 1) (g ^ d)‖ ≤ ρ := by
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hρ fun d hd => ?_
        have hd1 := Finset.ne_of_mem_erase hd
        rcases Nat.lt_or_ge d 2 with hd2 | hd2
        · obtain rfl : d = 0 := by omega
          rw [hf0, zero_mul, norm_zero]; exact hρ
        obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
        rw [norm_mul]
        calc ‖coeff (k + 2) f‖ * ‖coeff (m + 1) (g ^ (k + 2))‖ ≤ ‖coeff (k + 2) f‖ * ρ ^ (k + 2) :=
              mul_le_mul_of_nonneg_left (norm_coeff_succ_pow_le g hg0 ρ m hρ ih' k) (norm_nonneg _)
          _ ≤ ρ := hf _ (by omega)
      have hgm : coeff (m + 1) g = coeff (m + 1) (subst g f) -
          ∑ d ∈ (Finset.range (m + 1 + 1)).erase 1, coeff d f * coeff (m + 1) (g ^ d) := by
        rw [hs]; ring
      rw [hgm, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy _ hm) ?_)
      rwa [norm_neg]
  exact fun n hn => key n hn n le_rfl

theorem norm_coeff_hondaSum_le (τ : K →+* K) (q : ℕ) (hq : 2 ≤ q) (c : ℕ → K) (f : K⟦X⟧) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hc0 : ‖c 0‖ ≤ ρ) (hf1 : coeff 1 f = 1) (n : ℕ) (hn : n ≤ q) :
    ‖coeff n (hondaSum τ q c f)‖ ≤ ρ := by
  unfold hondaSum
  rw [coeff_mk]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hρ fun j hj => ?_
  have hjn := Finset.mem_range.mp hj
  unfold frobOp
  rw [coeff_subst_X_pow (pow_ne_zero _ (by omega))]
  split_ifs with hdvd
  · have hle := Nat.le_of_dvd (by omega) hdvd
    have hqq : q < q ^ 2 := by rw [sq]; nlinarith
    have hj0 : j = 0 := by
      by_contra hj0
      have : q ^ 2 ≤ q ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    subst hj0
    have hnq : n = q := by rw [zero_add, pow_one] at hle; omega
    subst hnq
    simpa [Nat.div_self (by omega : 0 < n), coeff_map, hf1] using hc0
  · rw [mul_zero, norm_zero]; exact hρ

theorem norm_first_coeff_eq_one : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ)
    (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) →
    CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) →
    (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) → ‖c 0‖ = 1 := by
  intro K _ _ _ l σ hU f e hIL c hc hH hex
  obtain ⟨hp, hl2, hl1, hmax, -, -⟩ := hU
  obtain ⟨⟨hf0, hf1, he0, -, hef⟩, hder, -⟩ := hIL
  have hρ : 0 ≤ ‖(l : K)‖ := norm_nonneg _
  by_contra hne
  have hc0 : ‖c 0‖ ≤ ‖(l : K)‖ := hmax _ (lt_of_le_of_ne (hc 0) hne)
  have hf0' : coeff 0 f = 0 := by rw [coeff_zero_eq_constantCoeff_apply, hf0]
  have hlf0 : constantCoeff (C (l : K) * f) = 0 := by simp [hf0]
  have hg0 : constantCoeff (Formalism.L2.Th1.C.mulBy f e (l : K)) = 0 := by
    unfold Formalism.L2.Th1.C.mulBy
    exact constantCoeff_subst_eq_zero hlf0 e he0
  have hfg : subst (Formalism.L2.Th1.C.mulBy f e (l : K)) f = C (l : K) * f := by
    unfold Formalism.L2.Th1.C.mulBy
    rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' he0)
      (HasSubst.of_constantCoeff_zero' hlf0), hef, subst_X (HasSubst.of_constantCoeff_zero' hlf0)]
  have hy : ∀ n ≤ l ^ 2, ‖coeff n (subst (Formalism.L2.Th1.C.mulBy f e (l : K)) f)‖ ≤ ‖(l : K)‖ := by
    intro n hn
    rw [hfg]
    have h1 := hH n
    have h2 := norm_coeff_hondaSum_le (σ ^ 2) (l ^ 2) (by nlinarith) c f _ hρ hc0 hf1 n hn
    have : coeff n (C (l : K) * f) = coeff n (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) +
        coeff n (hondaSum (σ ^ 2) (l ^ 2) c f) := by rw [map_sub]; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  have hg := norm_coeff_le_of_subst f _ _ hρ hf0' hf1 (coeff_mul_pow_le l hp hl1 f hder) hg0 _ hy
  obtain ⟨n, hn, hn1⟩ := hex
  have := hg n hn
  linarith

end GlobalTheory.Honda.HeightTwo
