import Formalism.GaussJetBounds.StatementN
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

section PairJetAux

lemma mfact_eq_prod_univ {σ : Type} [Fintype σ] (κ : σ →₀ ℕ) :
    mfact κ = ∏ x, (κ x).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => rfl)

lemma mfact_mul_dvd {σ : Type} [Fintype σ] (μ ν : σ →₀ ℕ) :
    mfact μ * mfact ν ∣ mfact (μ + ν) := by
  rw [mfact_eq_prod_univ, mfact_eq_prod_univ, mfact_eq_prod_univ, ← Finset.prod_mul_distrib]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun x _ =>
    Nat.factorial_mul_factorial_dvd_factorial_add _ _

def pairExp {ι : Type} [Fintype ι] (n : ι → ℕ) : (Bool × ι) →₀ ℕ :=
  ∑ i, n i • (Finsupp.single (false, i) 1 + Finsupp.single (true, i) 1)

lemma pairExp_apply {ι : Type} [Fintype ι] (n : ι → ℕ) (b : Bool) (i : ι) :
    pairExp n (b, i) = n i := by
  classical
  unfold pairExp
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · cases b <;> simp
  · intro j _ hj
    cases b <;> simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma mfact_pairExp {ι : Type} [Fintype ι] (n : ι → ℕ) :
    mfact (pairExp n) = (∏ i, (n i).factorial) * ∏ i, (n i).factorial := by
  classical
  rw [mfact_eq_prod_univ, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [pairExp_apply]

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

lemma quad_pow {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → K) (k : ℕ) :
    (∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) :
      MvPowerSeries (Bool × ι) K) ^ k =
    ∑ n ∈ Finset.piAntidiag Finset.univ k, (Nat.multinomial Finset.univ n : MvPowerSeries (Bool × ι) K) *
      MvPowerSeries.monomial (pairExp n) (∏ i, u i ^ n i) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  unfold pairExp
  rw [← MvPowerSeries.prod_monomial]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← MvPowerSeries.monomial_pow]
  congr 1
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, ← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial]
  simp

lemma exp_jet (r : ℝ) (hr : 1 ≤ r) (ι : Type) [Fintype ι] (S : K) (u : ι → K) (hS : ‖S‖ ≤ r)
    (hu : ∀ i, ‖u i‖ ≤ 1) (κ : (Bool × ι) →₀ ℕ) :
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
        (mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
          MvPowerSeries.X (true, i)))‖ ≤ r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
  classical
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hQ0 : MvPowerSeries.constantCoeff ((-S) • ∑ i, MvPowerSeries.C (u i) *
      MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K) = 0 := by
    simp
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  unfold mvExp
  rw [PowerSeries.coeff_subst hs, mul_finsum]
  refine norm_finsum_le_of (pow_nonneg hr0 _) fun k => ?_
  rw [smul_pow, quad_pow, PowerSeries.coeff_exp, Finset.smul_sum, map_sum, Finset.smul_sum,
    Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun n hn => ?_
  rw [Finset.mem_piAntidiag] at hn
  have hk : ∑ i, n i = k := hn.1
  rw [← map_natCast (MvPowerSeries.C (σ := Bool × ι) (R := K)), ← MvPowerSeries.smul_eq_C_mul,
    map_smul, map_smul, MvPowerSeries.coeff_monomial]
  by_cases hκ : κ = pairExp n
  · rw [if_pos hκ]
    have hspec := Nat.multinomial_spec Finset.univ n
    rw [hk] at hspec
    have hk0 : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hval : ((mfact κ : ℕ) : K) * ((algebraMap ℚ K) (1 / (k.factorial : ℚ)) •
        ((-S) ^ k • ((Nat.multinomial Finset.univ n : ℕ) : K) • ∏ i, u i ^ n i)) =
        ((∏ i, (n i).factorial : ℕ) : K) * ((-S) ^ k * ∏ i, u i ^ n i) := by
      rw [hκ, mfact_pairExp, map_div₀, map_one, map_natCast, ← hspec]
      rw [← hspec] at hk0
      simp only [smul_eq_mul]
      push_cast at hk0 ⊢
      have hP := left_ne_zero_of_mul hk0
      have hM := right_ne_zero_of_mul hk0
      field_simp
    rw [hval, norm_mul, norm_mul, norm_pow, norm_neg, norm_prod]
    have h1 : ‖((∏ i, (n i).factorial : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
    have h2 : ∏ i, ‖u i ^ n i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hu i)
    have h3 : ‖S‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg _) hS k
    have h4 : ∑ i, min (κ (false, i)) (κ (true, i)) = k := by
      rw [hκ, ← hk]
      simp only [pairExp_apply, min_self]
    rw [h4]
    calc ‖((∏ i, (n i).factorial : ℕ) : K)‖ * (‖S‖ ^ k * ∏ i, ‖u i ^ n i‖)
        ≤ 1 * (r ^ k * 1) := by
          apply mul_le_mul h1 _ (by positivity) zero_le_one
          exact mul_le_mul h3 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (pow_nonneg hr0 _)
      _ = r ^ k := by ring
  · rw [if_neg hκ]
    simp only [smul_zero, mul_zero, norm_zero]
    exact pow_nonneg hr0 _

end PairJetAux

theorem pair_jet_bound : PairJet.{u} := by
  intro K _ _ _ pi h0 h1 ι _ S u hS hu sg hsg κ
  classical
  set r : ℝ := pi ^ (-(1 / 2 : ℝ)) with hrdef
  have hr : 1 ≤ r := Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1.le (by norm_num)
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hrhs : pi ^ (-(1 / 2 : ℝ) * ∑ i, (min (κ (false, i)) (κ (true, i)) : ℝ)) =
      r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
    rw [Real.rpow_mul h0.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    rfl
  rw [hrhs, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  obtain ⟨c, hc⟩ := mfact_mul_dvd p.1 p.2
  rw [hp] at hc
  have hE := exp_jet r hr ι S u hS hu p.1
  have hG := hsg p.2
  have hcn : ‖((c : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
  set E := mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
          MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K)
  have hre : ((mfact κ : ℕ) : K) * (MvPowerSeries.coeff p.1 E * MvPowerSeries.coeff p.2 sg) =
      (((mfact p.1 : ℕ) : K) * MvPowerSeries.coeff p.1 E) *
        ((((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg) * ((c : ℕ) : K)) := by
    rw [hc]; push_cast; ring
  rw [hre, norm_mul, norm_mul (((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg)]
  have hmono : r ^ (∑ i, min (p.1 (false, i)) (p.1 (true, i))) ≤
      r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
    apply pow_le_pow_right₀ hr
    apply Finset.sum_le_sum fun i _ => ?_
    rw [← hp]
    simp only [Finsupp.add_apply]
    omega
  calc _ ≤ r ^ (∑ i, min (p.1 (false, i)) (p.1 (true, i))) * (1 * 1) := by
        apply mul_le_mul hE _ (by positivity) (pow_nonneg hr0 _)
        exact mul_le_mul hG hcn (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [mul_one, mul_one]; exact hmono

end Formalism.DworkPowerSeriesWeights
