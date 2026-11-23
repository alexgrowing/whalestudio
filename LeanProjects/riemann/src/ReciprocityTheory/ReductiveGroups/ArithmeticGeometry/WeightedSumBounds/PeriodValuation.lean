import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne

namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps

open ReciprocityTheory.PGsh PowerSeries

noncomputable section

section Coeff

variable {K : Type*} [Field K]

theorem coeff_pow_gap (f : PowerSeries K) (M : ℕ) (hM : 2 ≤ M) (a : K)
    (h0 : coeff 0 f = 0) (h1 : coeff 1 f = a) (hg : ∀ j, 2 ≤ j → j < M → coeff j f = 0)
    (n : ℕ) (hn : 2 ≤ n) : coeff M (f ^ n) = if n = M then a ^ M else 0 := by
  have hX : (X : PowerSeries K) ∣ f :=
    X_dvd_iff.mpr (by rw [← coeff_zero_eq_constantCoeff_apply]; exact h0)
  obtain ⟨g, rfl⟩ := hX
  have hg0 : coeff 0 g = a := by
    rw [← h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]
  have hd : (X : PowerSeries K) ^ (M - 1) ∣ g - C a := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, coeff_C]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [hg0]
    · rw [if_neg hm0.ne', sub_zero, ← coeff_succ_X_mul]
      exact hg (m + 1) (by omega) (by omega)
  have hdn : (X : PowerSeries K) ^ (M - 1) ∣ g ^ n - C a ^ n :=
    dvd_trans hd (sub_dvd_pow_sub_pow _ _ n)
  rw [mul_pow, coeff_X_pow_mul']
  by_cases hle : n ≤ M
  · rw [if_pos hle]
    by_cases heq : n = M
    · subst heq
      rw [if_pos rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow,
        ← coeff_zero_eq_constantCoeff_apply, hg0]
    · rw [if_neg heq]
      have h1' := (X_pow_dvd_iff.mp hdn) (M - n) (by omega)
      rw [map_sub, ← map_pow, coeff_C, if_neg (by omega), sub_zero] at h1'
      exact h1'
  · rw [if_neg hle, if_neg (by omega)]

theorem coeff_subst_gap (lg P : PowerSeries K) (M : ℕ) (hM : 2 ≤ M) (b : K)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1) (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0)
    (hP0 : coeff 0 P = 0) (hP1 : coeff 1 P = b) (hPg : ∀ j, 2 ≤ j → j < M → coeff j P = 0) :
    coeff M (subst P lg) = coeff M P + coeff M lg * b ^ M := by
  have hs : HasSubst P :=
    HasSubst.of_constantCoeff_zero' (by rw [← coeff_zero_eq_constantCoeff_apply]; exact hP0)
  rw [coeff_subst' hs]
  have hsupp : (Function.support fun d : ℕ => coeff d lg • coeff M (P ^ d)) ⊆
      ↑(Finset.range (M + 1)) := by
    intro d hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    simp only
    rw [coeff_pow_gap P M hM b hP0 hP1 hPg d (by omega), if_neg (by omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_range_succ,
    Finset.sum_eq_single 1]
  · rw [coeff_pow_gap P M hM b hP0 hP1 hPg M hM, if_pos rfl]
    simp [hl1]
  · intro d hd hd1
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 0 := by omega
      subst this; rw [hl0, zero_smul]
    · rw [hlg d h (Finset.mem_range.mp hd), zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem coeff_expComp_gap [CharZero K] (Ω : K) (lg : PowerSeries K) (M : ℕ) (hM : 2 ≤ M)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1)
    (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0) :
    coeff M (expComp Ω lg) = Ω * coeff M lg + Ω ^ M / (M.factorial : K) := by
  rw [expComp, coeff_mk, Finset.sum_range_succ, Finset.sum_eq_single 1]
  · rw [coeff_pow_gap lg M hM 1 hl0 hl1 hlg M hM, if_pos rfl]
    simp
  · intro d hd hd1
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 0 := by omega
      have hM0 : M ≠ 0 := by omega
      subst this; simp [coeff_one, hM0]
    · rw [coeff_pow_gap lg M hM 1 hl0 hl1 hlg d h,
        if_neg (by have := Finset.mem_range.mp hd; omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem coeff_eq_zero_of_symm [IsAlgClosed K] [CharZero K] (lg : PowerSeries K) (M : ℕ)
    (hM : 2 ≤ M) (h : ∀ z : K, z ^ (M - 1) = 1 → rescale z lg = z • lg) (j : ℕ)
    (hj2 : 2 ≤ j) (hj : j < M) : coeff j lg = 0 := by
  have hN : M - 1 ≠ 0 := by omega
  have : NeZero ((M - 1 : ℕ) : K) := ⟨Nat.cast_ne_zero.mpr hN⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (M - 1) K)
    (Polynomial.degree_cyclotomic_pos (M - 1) K (Nat.pos_of_ne_zero hN)).ne'
  have hzp : IsPrimitiveRoot z (M - 1) := Polynomial.isRoot_cyclotomic_iff.mp hz
  have hc := congrArg (coeff j) (h z hzp.pow_eq_one)
  rw [coeff_rescale, coeff_smul, smul_eq_mul] at hc
  by_contra hne
  have hz0 : z ≠ 0 := hzp.ne_zero hN
  have h1 : z ^ (j - 1) = 1 := by
    have h2 : z ^ j = z := mul_right_cancel₀ hne hc
    have hj' : j = (j - 1) + 1 := by omega
    rw [hj', pow_succ] at h2
    have h3 : z ^ (j - 1) * z = 1 * z := by rw [one_mul]; exact h2
    exact mul_right_cancel₀ hz0 h3
  have := Nat.le_of_dvd (by omega) (hzp.dvd_of_pow_eq_one _ h1)
  omega

end Coeff

section Val

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

theorem exists_real {x : K} (hx : x ≠ 0) : ∃ r : ℝ, v x = r := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((v.top_iff).not.mpr hx)
  exact ⟨r, hr.symm⟩

theorem nsmul_one_coe (n : ℕ) : n • (1 : WithTop ℝ) = ((n : ℝ) : WithTop ℝ) := by
  rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]

theorem natCast_nonneg (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact v.map_le_add ih (le_of_eq v.map_one.symm)

theorem intCast_nonneg (n : ℤ) : 0 ≤ v (n : K) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using natCast_nonneg v m
  · simpa [v.map_neg] using natCast_nonneg v m

theorem natCast_eq_zero_of_coprime {p : ℕ} (hp1 : v (p : K) = 1) {c : ℕ}
    (hc : Nat.Coprime p c) : v (c : K) = 0 := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have hK : (a : K) * p + b * c = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
  have h0 := natCast_nonneg v c
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have h1 : 0 < v ((a : K) * p) := by
    rw [v.map_mul, hp1]
    calc (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
      _ = 0 + 1 := (zero_add 1).symm
      _ ≤ v (a : K) + 1 := add_le_add_left (intCast_nonneg v a) 1
  have h2 : 0 < v ((b : K) * c) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_left (intCast_nonneg v b))
  have h3 := v.map_add ((a : K) * p) ((b : K) * c)
  rw [hK, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))

theorem natCast_eq_factorization {p : ℕ} (hp : p.Prime) (hp1 : v (p : K) = 1) {m : ℕ}
    (hm : m ≠ 0) : v (m : K) = ((m.factorization p : ℝ) : WithTop ℝ) := by
  have e := Nat.ordProj_mul_ordCompl_eq_self m p
  have hc := Nat.coprime_ordCompl hp hm
  conv_lhs => rw [← e]
  rw [Nat.cast_mul, Nat.cast_pow, v.map_mul, v.map_pow, hp1,
    natCast_eq_zero_of_coprime v hp1 hc, add_zero, nsmul_one_coe]

theorem factorization_factorial_sq {p : ℕ} (hp : p.Prime) :
    (p ^ 2).factorial.factorization p = p + 1 := by
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp,
    padicValNat_factorial (p := p) (n := p ^ 2) (b := 3) (by rw [Nat.log_pow hp.one_lt]; norm_num)]
  have h1 : p ^ 2 / p ^ 1 = p := by rw [pow_one, pow_two, Nat.mul_div_cancel _ hp.pos]
  have h2 : p ^ 2 / p ^ 2 = 1 := Nat.div_self (pow_pos hp.pos 2)
  rw [show Finset.Ico 1 3 = {1, 2} by decide, Finset.sum_pair (by norm_num), h1, h2]

theorem factorization_factorial_self {p : ℕ} (hp : p.Prime) :
    p.factorial.factorization p = 1 := by
  have := Fact.mk hp
  have hl : Nat.log p p = 1 := by
    have := Nat.log_pow hp.one_lt 1
    rwa [pow_one] at this
  rw [Nat.factorization_def _ hp,
    padicValNat_factorial (p := p) (n := p) (b := 2) (by rw [hl]; norm_num)]
  rw [show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, pow_one, Nat.div_self hp.pos]

theorem eq_of_nonneg_add {x y : K} {A B : ℝ} (hA : A < 0) (hx : v x = A) (hy : v y = B)
    (h : 0 ≤ v (x + y)) : A = B := by
  by_contra hne
  have hd : v x ≠ v y := by rw [hx, hy]; exact fun e => hne (WithTop.coe_injective e)
  rw [v.map_add_of_distinct_val hd, hx, hy, ← WithTop.coe_min] at h
  have h' : (0 : ℝ) ≤ min A B := by exact_mod_cast h
  exact absurd h' (not_le.mpr (lt_of_le_of_lt (min_le_left A B) hA))

theorem add_eq_of_lt {x y : K} {A B : ℝ} (hx : v x = A) (hy : v y = B) (h : A < B) :
    v (x + y) = A := by
  have hd : v x ≠ v y := by rw [hx, hy]; exact fun e => h.ne (WithTop.coe_injective e)
  rw [v.map_add_of_distinct_val hd, hx, hy, ← WithTop.coe_min, min_eq_left h.le]

theorem div_eq_coe {x y : K} (hy : y ≠ 0) {A B : ℝ} (hx : v x = A) (hyv : v y = B) :
    v (x / y) = ((A - B : ℝ) : WithTop ℝ) := by
  obtain ⟨c, hc⟩ := exists_real v (inv_ne_zero hy)
  have h1 : v (y * y⁻¹) = 0 := by rw [mul_inv_cancel₀ hy, v.map_one]
  rw [v.map_mul, hyv, hc, ← WithTop.coe_add] at h1
  have h2 : B + c = 0 := WithTop.coe_eq_zero.mp h1
  rw [div_eq_mul_inv, v.map_mul, hx, hc, ← WithTop.coe_add]
  congr 1
  linarith

end Val

section ZetaNonvanishing₂

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

theorem v_one_sub_le {ζ μ : K} {k : ℕ} (hk : k ≠ 0) (hζ : ζ ^ k = 1) (i : ℕ)
    (hμ : μ = ζ ^ i) : v (1 - ζ) ≤ v (1 - μ) := by
  have hv0 : v ζ = 0 := v_eq_zero_of_pow_eq_one (v := v) hk hζ
  have e : 1 - μ = (1 - ζ) * ∑ j ∈ Finset.range i, ζ ^ j := by
    rw [hμ]; linear_combination (geom_sum_mul ζ i)
  rw [e, v.map_mul]
  refine le_add_of_nonneg_right (v.map_le_sum fun j _ => ?_)
  rw [v.map_pow, hv0, smul_zero]

theorem v_zeta_sub_one {p : ℕ} (hp : p.Prime) (hp1 : v (p : K) = 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) = ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) := by
  classical
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hall : ∀ μ ∈ primitiveRoots p K, v (1 - μ) = v (1 - ζ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.pos).mp hμ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    exact le_antisymm (v_one_sub_le v hp.ne_zero hμ'.pow_eq_one j hj.symm)
      (v_one_sub_le v hp.ne_zero hζ.pow_eq_one i hi.symm)
  have hprod : (p : K) = ∏ μ ∈ primitiveRoots p K, (1 - μ) := by
    have := congrArg (Polynomial.eval (1 : K))
      (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at this
    simpa using this
  have hsum : ∀ s : Finset K, (∀ μ ∈ s, v (1 - μ) = v (1 - ζ)) →
      v (∏ μ ∈ s, (1 - μ)) = s.card • v (1 - ζ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro h
      rw [Finset.prod_insert ha, v.map_mul, h a (Finset.mem_insert_self a s),
        ih (fun μ hμ => h μ (Finset.mem_insert_of_mem hμ)), Finset.card_insert_of_notMem ha,
        succ_nsmul']
  have hcard : (primitiveRoots p K).card = p - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hp]
  have hmain : v (p : K) = (p - 1) • v (1 - ζ) := by rw [hprod, hsum _ hall, hcard]
  have hne : (1 : K) - ζ ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hp.one_lt).symm
  obtain ⟨r, hr⟩ := exists_real v hne
  rw [hp1, hr, ← WithTop.coe_nsmul, ← WithTop.coe_one] at hmain
  have hr' : (1 : ℝ) = (p - 1 : ℕ) • r := WithTop.coe_injective hmain
  have e : ζ - 1 = -(1 - ζ) := by ring
  rw [e, v.map_neg, hr]
  congr 1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [nsmul_eq_mul, Nat.cast_sub hp.one_le, Nat.cast_one] at hr'
  rw [eq_div_iff (by linarith)]
  linarith

end ZetaNonvanishing₂

end

end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
