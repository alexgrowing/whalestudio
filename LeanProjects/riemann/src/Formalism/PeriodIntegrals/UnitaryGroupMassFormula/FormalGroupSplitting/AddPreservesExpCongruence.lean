import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Development

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit MvPowerSeries Finset

variable {K : Type} [Field K] {σ : Type}

theorem deg_eq (α : σ →₀ ℕ) : (α.sum fun _ k => k) = Finsupp.degree α := by rfl

private theorem coeff_pow_eq_zero_of_degree_lt_formal_group_splitting {f : MvPowerSeries σ K} (hf : constantCoeff f = 0) :
    ∀ (n : ℕ) {α : σ →₀ ℕ}, Finsupp.degree α < n → coeff α (f ^ n) = 0 := by
  classical
  intro n
  induction n with
  | zero => intro α h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro α h
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h2 : p.2 = 0
    · rw [h2, coeff_zero_eq_constantCoeff_apply, hf, mul_zero]
    · have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
        rw [← hp, map_add]
      have h2' : 0 < Finsupp.degree p.2 := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        exact h2 ((Finsupp.degree_eq_zero_iff _).mp h0)
      rw [ih (by omega), zero_mul]

theorem coeff_pow_mul_pow_eq_zero {f g : MvPowerSeries σ K} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) {i j : ℕ} {α : σ →₀ ℕ} (h : Finsupp.degree α < i + j) :
    coeff α (f ^ i * g ^ j) = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
    rw [← hp, map_add]
  by_cases h1 : Finsupp.degree p.1 < i
  · rw [coeff_pow_eq_zero_of_degree_lt_formal_group_splitting hf i h1, zero_mul]
  · rw [coeff_pow_eq_zero_of_degree_lt_formal_group_splitting hg j (by omega), mul_zero]

theorem coeff_pow_eq_zero' {f : MvPowerSeries σ K} (hf : constantCoeff f = 0) {n : ℕ}
    {α : σ →₀ ℕ} (h : Finsupp.degree α < n) : coeff α (f ^ n) = 0 := by
  exact coeff_pow_eq_zero_of_degree_lt_formal_group_splitting hf n h

def expT (f : MvPowerSeries σ K) (N : ℕ) : MvPowerSeries σ K :=
  ∑ n ∈ range N, ((n.factorial : K)⁻¹) • f ^ n

theorem coeff_expT (f : MvPowerSeries σ K) (N : ℕ) (α : σ →₀ ℕ) :
    coeff α (expT f N) = ∑ n ∈ range N, coeff α (f ^ n) / (n.factorial : K) := by
  simp only [expT, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]

theorem coeff_expMv_eq_expT {f : MvPowerSeries σ K} (hf : constantCoeff f = 0) {α : σ →₀ ℕ}
    {N : ℕ} (hN : Finsupp.degree α < N) : coeff α (expMv f) = coeff α (expT f N) := by
  rw [coeff_expT]
  change (∑ n ∈ range ((α.sum fun _ k => k) + 1), coeff α (f ^ n) / (n.factorial : K)) = _
  rw [deg_eq]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_range] at hn ⊢
    omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [coeff_pow_eq_zero' hf (by omega), zero_div]

private theorem coeff_expT_add_eq_coeff_expT_mul_expT [CharZero K] {f g : MvPowerSeries σ K} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) {α : σ →₀ ℕ} {N : ℕ} (hN : Finsupp.degree α < N) :
    coeff α (expT (f + g) N) = coeff α (expT f N * expT g N) := by
  set F : ℕ → ℕ → K := fun i j =>
    coeff α (f ^ i * g ^ j) / ((i.factorial : K) * (j.factorial : K)) with hF
  have hfac : ∀ n : ℕ, (n.factorial : K) ≠ 0 := fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have lhs : coeff α (expT (f + g) N) = ∑ n ∈ range N, ∑ m ∈ range (n + 1), F m (n - m) := by
    rw [coeff_expT]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_pow, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hc : ((n.choose m : ℕ) : K) * (m.factorial : K) * ((n - m).factorial : K) =
        (n.factorial : K) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmn
    rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)), coeff_mul_C]
    show _ = coeff α (f ^ m * g ^ (n - m)) / ((m.factorial : K) * ((n - m).factorial : K))
    rw [← hc]
    have := hfac m
    have := hfac (n - m)
    have hch : ((n.choose m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hmn).ne'
    field_simp
  have rhs : coeff α (expT f N * expT g N) = ∑ i ∈ range N, ∑ j ∈ range N, F i j := by
    simp only [expT]
    rw [Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, map_smul, smul_eq_mul]
    show _ = coeff α (f ^ i * g ^ j) / ((i.factorial : K) * (j.factorial : K))
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [lhs, rhs, Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    show coeff α (f ^ i * g ^ j) / _ = 0
    rw [coeff_pow_mul_pow_eq_zero hf hg (by omega), zero_div]

theorem expMv_add [CharZero K] {f g : MvPowerSeries σ K} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by
  classical
  ext α
  have hfg : constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  rw [coeff_expMv_eq_expT hfg (Nat.lt_succ_self (Finsupp.degree α)), coeff_mul]
  have key : ∀ p ∈ antidiagonal α, coeff p.1 (expMv f) * coeff p.2 (expMv g) =
      coeff p.1 (expT f (Finsupp.degree α + 1)) * coeff p.2 (expT g (Finsupp.degree α + 1)) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
      rw [← hp, map_add]
    rw [coeff_expMv_eq_expT hf (N := Finsupp.degree α + 1) (by omega),
      coeff_expMv_eq_expT hg (N := Finsupp.degree α + 1) (by omega)]
  rw [Finset.sum_congr rfl key, ← coeff_mul]
  exact coeff_expT_add_eq_coeff_expT_mul_expT hf hg (Nat.lt_succ_self _)

theorem simeqW_add [CharZero K] {W : Subring K} {f g f' g' : MvPowerSeries σ K}
    (h : SimeqW W f g) (h' : SimeqW W f' g') : SimeqW W (f + f') (g + g') := by
  classical
  obtain ⟨h0, hW⟩ := h
  obtain ⟨h0', hW'⟩ := h'
  have e : f + f' - (g + g') = (f - g) + (f' - g') := by ring
  refine ⟨by rw [e, map_add, h0, h0', add_zero], fun n => ?_⟩
  rw [e, expMv_add h0 h0', coeff_mul]
  exact W.sum_mem fun p _ => W.mul_mem (hW _) (hW' _)

theorem addPreservesExpCongruence : S3 := by
  intro K _ _ W σ f g f' g' h h'
  exact simeqW_add h h'

end PI.FglPhSplit.Wk

end
