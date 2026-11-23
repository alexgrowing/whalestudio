import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IntBinomScalar

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.C

variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem hasSubst_of_cc {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf

private theorem finsupp_degree_add (a b : σ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add Finsupp.degree a b
  | exact Finsupp.degree_add a b
  | simp [Finsupp.degree_add]

private theorem coeff_mul_eq_zero_of_degree_lt_add' {A B : MvPowerSeries σ K} {a b : ℕ}
    (hA : ∀ m : σ →₀ ℕ, m.degree < a → MvPowerSeries.coeff m A = 0)
    (hB : ∀ m : σ →₀ ℕ, m.degree < b → MvPowerSeries.coeff m B = 0)
    (n : σ →₀ ℕ) (hn : n.degree < a + b) : MvPowerSeries.coeff n (A * B) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  | simp only [Finset.mem_antidiagonal] at hp
  | simp at hp
  have hd : p.1.degree + p.2.degree = n.degree := by rw [← finsupp_degree_add, hp]
  by_cases h1 : p.1.degree < a
  · rw [hA _ h1, zero_mul]
  · rw [hB _ (by omega), mul_zero]

private theorem coeff_pow_eq_zero_of_degree_lt_mul {A : MvPowerSeries σ K} {a : ℕ}
    (hA : ∀ m : σ →₀ ℕ, m.degree < a → MvPowerSeries.coeff m A = 0) (k : ℕ) :
    ∀ n : σ →₀ ℕ, n.degree < k * a → MvPowerSeries.coeff n (A ^ k) = 0 := by
  induction k with
  | zero => intro n hn; simp at hn
  | succ k ih =>
    intro n hn
    rw [pow_succ']
    have e : (k + 1) * a = a + k * a := by ring
    exact coeff_mul_eq_zero_of_degree_lt_add' hA ih n (by rw [e] at hn; exact hn)

theorem coeff_pow_eq_zero_of_cc {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    {n : σ →₀ ℕ} {k : ℕ} (h : n.degree < k) : MvPowerSeries.coeff n (f ^ k) = 0 := by
  have h1 : ∀ m : σ →₀ ℕ, m.degree < 1 → MvPowerSeries.coeff m f = 0 := by
    intro m hm
    have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
    subst hm0
    simpa using hf
  exact coeff_pow_eq_zero_of_degree_lt_mul h1 k n (by simpa using h)

theorem coeff_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    {n : σ →₀ ℕ} {N : ℕ} (hN : n.degree < N) :
    MvPowerSeries.coeff n (mvExp f) =
      ∑ k ∈ range N, ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ k) := by
  classical
  unfold mvExp
  rw [PowerSeries.coeff_subst (hasSubst_of_cc hf),
    finsum_eq_sum_of_support_subset _ (s := Finset.range N) ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [PowerSeries.coeff_exp]
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hkN
    apply hk
    simp [coeff_pow_eq_zero_of_cc hf (show n.degree < k by omega)]

theorem mvExp_zero : mvExp (0 : MvPowerSeries σ K) = 1 := by
  classical
  ext n
  rw [coeff_mvExp (map_zero _) (Nat.lt_succ_self n.degree), Finset.sum_range_succ']
  simp

theorem constantCoeff_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  have h := coeff_mvExp hf (n := 0) (N := 1) (by simp)
  simpa using h

private theorem coeff_mvExp_eq_coeff_trunc_sum {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (N : ℕ) (m : σ →₀ ℕ) (hm : m.degree < N) :
    MvPowerSeries.coeff m (mvExp f) =
      MvPowerSeries.coeff m (∑ k ∈ Finset.range N, ((k.factorial : K))⁻¹ • f ^ k) := by
  rw [coeff_mvExp hf hm, map_sum]
  simp only [map_smul, smul_eq_mul]

private theorem coeff_mul_congr_of_degree_lt {A A' B B' : MvPowerSeries σ K} {N : ℕ}
    (hA : ∀ m : σ →₀ ℕ, m.degree < N → MvPowerSeries.coeff m A = MvPowerSeries.coeff m A')
    (hB : ∀ m : σ →₀ ℕ, m.degree < N → MvPowerSeries.coeff m B = MvPowerSeries.coeff m B')
    (n : σ →₀ ℕ) (hn : n.degree < N) :
    MvPowerSeries.coeff n (A * B) = MvPowerSeries.coeff n (A' * B') := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  | simp only [Finset.mem_antidiagonal] at hp
  | simp at hp
  have hd : p.1.degree + p.2.degree = n.degree := by rw [← finsupp_degree_add, hp]
  rw [hA _ (by omega), hB _ (by omega)]

theorem pderiv_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (i : σ) :
    MvPowerSeries.pderiv K i (mvExp f) = MvPowerSeries.pderiv K i f * mvExp f := by
  classical
  ext n
  have hE : MvPowerSeries.pderiv K i
      (∑ k ∈ Finset.range (n.degree + 1 + 1), ((k.factorial : K))⁻¹ • f ^ k) =
      MvPowerSeries.pderiv K i f *
        ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K))⁻¹ • f ^ k := by
    rw [map_sum, Finset.mul_sum, Finset.sum_range_succ' _ (n.degree + 1)]
    have h0 : MvPowerSeries.pderiv K i (((Nat.factorial 0 : K))⁻¹ • f ^ 0) = 0 := by simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : (((k + 1).factorial : K))⁻¹ * ((k + 1 : ℕ) : K) = ((k.factorial : K))⁻¹ := by
      rw [Nat.factorial_succ]
      push_cast
      have : (k.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      field_simp
    rw [Derivation.map_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, ← Nat.cast_smul_eq_nsmul K,
      smul_smul, hc, mul_smul_comm, mul_comm (MvPowerSeries.pderiv K i f)]
  rw [MvPowerSeries.coeff_pderiv, coeff_mvExp_eq_coeff_trunc_sum hf (n.degree + 1 + 1) _ ?_,
    ← MvPowerSeries.coeff_pderiv, hE]
  · exact coeff_mul_congr_of_degree_lt (fun _ _ => rfl) (fun m hm => (coeff_mvExp_eq_coeff_trunc_sum hf _ m hm).symm) n
      (Nat.lt_succ_self _)
  · rw [finsupp_degree_add, Finsupp.degree_single]
    omega

private theorem inv_factorial_mul_choose_eq {k m : ℕ} (h : m ≤ k) :
    ((k.factorial : K))⁻¹ * (k.choose m : K) =
      ((m.factorial : K))⁻¹ * (((k - m).factorial : K))⁻¹ := by
  have e := Nat.choose_mul_factorial_mul_factorial h
  have h1 : (m.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have h2 : ((k - m).factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (k.choose m : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
  rw [← e]
  push_cast
  first
  | (field_simp; done)
  | (field_simp; ring)

private theorem mvExp_add_binomial_series_coefficients {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := by
  classical
  have hfg : MvPowerSeries.constantCoeff (f + g) = 0 := by simp [hf, hg]
  ext n
  rw [coeff_mvExp hfg (Nat.lt_succ_self n.degree),
    coeff_mul_congr_of_degree_lt (coeff_mvExp_eq_coeff_trunc_sum hf (n.degree + 1)) (coeff_mvExp_eq_coeff_trunc_sum hg (n.degree + 1)) n
      (Nat.lt_succ_self _),
    Finset.sum_mul_sum, map_sum]
  simp only [map_sum, smul_mul_smul_comm, map_smul, smul_eq_mul]
  have hL : ∀ k ∈ Finset.range (n.degree + 1),
      ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n ((f + g) ^ k) =
        ∑ m ∈ Finset.range (k + 1), ((m.factorial : K))⁻¹ * (((k - m).factorial : K))⁻¹ *
          MvPowerSeries.coeff n (f ^ m * g ^ (k - m)) := by
    intro k _
    rw [add_pow, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)) (k.choose m),
      mul_comm _ (MvPowerSeries.C _), MvPowerSeries.coeff_C_mul, ← mul_assoc, inv_factorial_mul_choose_eq hmk]
  rw [Finset.sum_congr rfl hL]
  have hflip := Finset.sum_range_diag_flip (n.degree + 1) (fun a b =>
    ((a.factorial : K))⁻¹ * ((b.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ a * g ^ b))
  try simp only at hflip
  rw [hflip]
  refine Finset.sum_congr rfl fun i hi => ?_
  refine Finset.sum_subset (fun j hj => Finset.mem_range.2
    (lt_of_lt_of_le (Finset.mem_range.1 hj) (Nat.sub_le _ _))) ?_
  intro j hj hj'
  simp only [Finset.mem_range, not_lt] at hi hj hj'
  rw [coeff_mul_eq_zero_of_degree_lt_add' (fun m hm => coeff_pow_eq_zero_of_cc hf hm)
    (fun m hm => coeff_pow_eq_zero_of_cc hg hm) n (by omega), mul_zero]

theorem mvExp_neg {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    mvExp (-f) * mvExp f = 1 := by
  have h := mvExp_add_binomial_series_coefficients (f := -f) (g := f) (by simp [hf]) hf
  rw [neg_add_cancel, mvExp_zero] at h
  exact h.symm

theorem mvExp_mul_neg {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    mvExp f * mvExp (-f) = 1 := by
  rw [mul_comm]
  exact mvExp_neg hf

theorem isUnit_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    IsUnit (mvExp f) := isUnit_iff_exists_inv.2 ⟨_, mvExp_mul_neg hf⟩

theorem mvExp_add {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := mvExp_add_binomial_series_coefficients hf hg

theorem mvExp_sub_mul {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f - g) * mvExp g = mvExp f := by
  rw [← mvExp_add (by simp [hf, hg]) hg, sub_add_cancel]

theorem mvExp_sum {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ K)
    (hf : ∀ a ∈ s, MvPowerSeries.constantCoeff (f a) = 0) :
    mvExp (∑ a ∈ s, f a) = ∏ a ∈ s, mvExp (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvExp_zero]
  | insert x s hx ih =>
    have hs : MvPowerSeries.constantCoeff (∑ a ∈ s, f a) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun b hb => hf b (Finset.mem_insert_of_mem hb)
    rw [Finset.sum_insert hx, Finset.prod_insert hx,
      mvExp_add (hf x (Finset.mem_insert_self x s)) hs,
      ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))]

theorem mvExp_nsmul {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (n : ℕ) :
    mvExp (n • f) = mvExp f ^ n := by
  induction n with
  | zero => simp [mvExp_zero]
  | succ n ih => rw [succ_nsmul, mvExp_add (by simp [hf]) hf, ih, pow_succ]

theorem mvExp_smul_nat {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (n : ℕ) :
    mvExp ((n : K) • f) = mvExp f ^ n := by
  rw [Nat.cast_smul_eq_nsmul]
  exact mvExp_nsmul hf n

private theorem eq_zero_of_mvExp_eq_one {h : MvPowerSeries σ K} (hh : MvPowerSeries.constantCoeff h = 0)
    (he : mvExp h = 1) : h = 0 := by
  classical
  by_contra hne
  have hex : ∃ d : ℕ, ∃ m : σ →₀ ℕ, m.degree = d ∧ MvPowerSeries.coeff m h ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (MvPowerSeries.ext fun m => by simpa using hall _ m rfl)
  obtain ⟨m, hmd, hm⟩ := Nat.find_spec hex
  have hmin : ∀ m' : σ →₀ ℕ, m'.degree < Nat.find hex → MvPowerSeries.coeff m' h = 0 := by
    intro m' hm'
    by_contra hc
    exact Nat.find_min hex hm' ⟨m', rfl, hc⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hm
    simpa using hh
  have hd1 : 1 ≤ Nat.find hex := by
    rw [← hmd]
    by_contra h0
    exact hm0 ((Finsupp.degree_eq_zero_iff m).1 (by omega))
  have he' := congrArg (MvPowerSeries.coeff m) he
  rw [coeff_mvExp hh (show m.degree < Nat.find hex + 1 by omega), Finset.sum_eq_single 1] at he'
  · simp [hm0, MvPowerSeries.coeff_one] at he'
    exact hm he'
  · intro k _ hk1
    rcases Nat.lt_or_gt_of_ne hk1 with hk0 | hk2
    · have hk : k = 0 := by omega
      subst hk
      simp [hm0, MvPowerSeries.coeff_one]
    · rw [coeff_pow_eq_zero_of_degree_lt_mul hmin k m (by rw [hmd]; nlinarith), mul_zero]
  · intro h1
    exact absurd (Finset.mem_range.2 (by omega)) h1

theorem mvExp_inj {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) (h : mvExp f = mvExp g) : f = g := by
  have h1 := mvExp_sub_mul hf hg
  rw [h] at h1
  have h2 : mvExp (f - g) = 1 := by
    calc mvExp (f - g) = mvExp (f - g) * mvExp g * mvExp (-g) := by
          rw [mul_assoc, mvExp_mul_neg hg, mul_one]
      _ = 1 := by rw [h1, mvExp_mul_neg hg]
  exact sub_eq_zero.1 (eq_zero_of_mvExp_eq_one (by simp [hf, hg]) h2)

theorem derivative_mvExp {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.derivative K (mvExp f : PowerSeries K) =
      PowerSeries.derivative K f * (mvExp f : PowerSeries K) := by
  unfold mvExp
  rw [PowerSeries.derivative_subst (hasSubst_of_cc hf), PowerSeries.derivative_exp, mul_comm]

theorem subst_mvExp {f : PowerSeries K} {a : MvPowerSeries σ K}
    (hf : PowerSeries.constantCoeff f = 0) (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst a (mvExp f : PowerSeries K) = mvExp (PowerSeries.subst a f) := by
  unfold mvExp
  exact PowerSeries.subst_comp_subst_apply (hasSubst_of_cc hf) (hasSubst_of_cc ha) _

theorem mvSubst_mvExp {τ : Type} {f : MvPowerSeries σ K} {a : σ → MvPowerSeries τ K}
    (hf : MvPowerSeries.constantCoeff f = 0) (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by
  unfold mvExp
  have hs : MvPowerSeries.HasSubst (fun _ : Unit => f) := by
    first
    | exact hasSubst_of_cc hf
    | exact (hasSubst_of_cc hf).const
    | exact PowerSeries.HasSubst.const (hasSubst_of_cc hf)
  first
  | exact MvPowerSeries.subst_comp_subst_apply hs ha _
  | (rw [PowerSeries.subst, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hs ha])

theorem rescale_mvExp {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) (c : K) :
    PowerSeries.rescale c (mvExp f : PowerSeries K) = mvExp (PowerSeries.rescale c f) := by
  unfold mvExp
  have hX : PowerSeries.HasSubst (c • PowerSeries.X : PowerSeries K) :=
    hasSubst_of_cc (by
      first
      | (simp; done)
      | (simp only [map_smul, smul_eq_zero]; right; exact PowerSeries.constantCoeff_X)
      | (simp [PowerSeries.X]; done))
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply (hasSubst_of_cc hf) hX]

theorem mvExp_sub {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f - g) = mvExp f * mvExp (-g) := by
  rw [sub_eq_add_neg]
  exact mvExp_add hf (by simp [hg])

theorem formalExpLaws' : MvExpLaws := by
  intro K _ _ σ
  exact ⟨mvExp_zero, fun f hf => constantCoeff_mvExp hf, fun f g hf hg => mvExp_add hf hg,
    fun f g hf hg h => mvExp_inj hf hg h⟩

theorem formalExpSubst' : MvExpSubst := by
  intro K _ _ σ f a hf ha
  exact subst_mvExp hf ha

end Formalism.L2.Th1.C
