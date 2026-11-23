import Formalism.TorsionNormIteration.InvIntegralOfClass
import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.CongrP

open Formalism.G

section Ring

variable {R : Type*} [CommRing R]

lemma coeff_subst_range (f a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    coeff N (f.subst a) = ∑ n ∈ Finset.range (N + 1), coeff n f * coeff N (a ^ n) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' ha)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1))]
  · simp [smul_eq_mul]
  · intro n hn
    simp only [Function.mem_support] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    obtain ⟨b, rfl⟩ := X_dvd_iff.mpr ha
    rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

lemma constantCoeff_trunc_succ (a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    constantCoeff (trunc (N + 1) a : PowerSeries R) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_coe_trunc_of_lt (Nat.succ_pos N),
    coeff_zero_eq_constantCoeff_apply, ha]

lemma coeff_subst_trunc (f a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    coeff N (f.subst (trunc (N + 1) a : PowerSeries R)) = coeff N (f.subst a) := by
  rw [coeff_subst_range f _ (constantCoeff_trunc_succ a ha N), coeff_subst_range f a ha]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [← coeff_coe_trunc_of_lt (Nat.lt_succ_self N) (f := (trunc (N + 1) a : PowerSeries R) ^ n),
    trunc_trunc_pow, coeff_coe_trunc_of_lt (Nat.lt_succ_self N)]

lemma sum_zero_pow_mul (n : ℕ) :
    ∑ i ∈ Finset.range n, (0 : R) ^ i * (0 : R) ^ (n - 1 - i) = if n = 1 then 1 else 0 := by
  rcases n with _ | n
  · simp
  · rw [Finset.sum_range_succ']
    simp only [pow_succ, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, pow_zero, one_mul]
    rcases n with _ | n <;> simp

lemma coeff_subst_add_C_mul_X_pow (f b : PowerSeries R) (hb : constantCoeff b = 0) (c : R)
    {N : ℕ} (hN : 1 ≤ N) :
    coeff N (f.subst (b + C c * X ^ N)) = coeff N (f.subst b) + coeff 1 f * c := by
  have he : constantCoeff (C c * X ^ N : PowerSeries R) = 0 := by
    rw [map_mul, map_pow, constantCoeff_X, zero_pow (by omega), mul_zero]
  have hbe : constantCoeff (b + C c * X ^ N) = 0 := by rw [map_add, hb, he, add_zero]
  have key : ∀ n : ℕ, coeff N ((b + C c * X ^ N) ^ n) = coeff N (b ^ n) + if n = 1 then c else 0 := by
    intro n
    have hg := geom_sum₂_mul (b + C c * X ^ N) b n
    have hx : (b + C c * X ^ N) ^ n = b ^ n + X ^ N * (C c * ∑ i ∈ Finset.range n,
        (b + C c * X ^ N) ^ i * b ^ (n - 1 - i)) := by
      rw [← sub_eq_iff_eq_add', ← hg]
      ring
    rw [hx, map_add, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_C, map_sum]
    simp only [map_mul, map_pow, hbe, hb]
    rw [sum_zero_pow_mul]
    split_ifs <;> simp
  rw [coeff_subst_range f _ hbe, coeff_subst_range f b hb]
  simp_rw [key, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  congr 1
  rw [Finset.sum_eq_single 1]
  · simp
  · intro n _ hn; simp [hn]
  · intro h; exfalso; apply h; simp; omega

end Ring

section Norm

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma mv_coeff_eq (φ : PowerSeries K) (d : Unit →₀ ℕ) :
    MvPowerSeries.coeff d φ = coeff (d ()) φ := by
  conv_lhs => rw [Finsupp.unique_single d]
  rfl

lemma integralMv_of (φ : PowerSeries K) (h : IntegralPS φ) : IntegralMv φ := fun d => by
  rw [mv_coeff_eq]; exact h _

lemma divByMv_of (x : K) (φ : PowerSeries K) (h : DivBy x φ) : DivByMv x φ := fun d => by
  rw [mv_coeff_eq]; exact h _

lemma norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa using IsUltrametricDist.norm_add_le_max a (-b)

theorem fwd (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) [CharZero K]
    {p q : ℕ} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ) {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hfe : IsFunEqType p q σ f) {α β : PowerSeries K}
    (hα0 : constantCoeff α = 0) (hβ0 : constantCoeff β = 0) (hα : IntegralPS α)
    (hβ : IntegralPS β) {r : ℕ} (hr : 1 ≤ r) (hd : DivBy ((p : K) ^ r) (α - β)) :
    DivBy ((p : K) ^ r) (f.subst α - f.subst β) := by
  intro N
  rw [map_sub, coeff_subst_range f α hα0, coeff_subst_range f β hβ0, ← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
  intro n _
  rw [← mul_sub, ← map_sub, norm_mul]
  obtain ⟨k, ⟨m, hm⟩, hk⟩ := h5 K p q σ hS f hf0 hfe n
  obtain ⟨h, hh0, hq⟩ := hS.2.1
  have hp1 : ‖(p : K)‖ ≤ 1 := hS.2.2.1.le
  have hpc := h6 K Unit p hS.1 α β (integralMv_of α hα) (integralMv_of β hβ) r hr
    (divByMv_of _ _ hd) (h * k) m (Finsupp.single () N)
  have hn : n = p ^ (h * k) * m := by rw [hm, hq, pow_mul]
  rw [mv_coeff_eq, ← hn] at hpc
  simp only [Finsupp.single_eq_same, norm_pow] at hpc
  have hkk : ‖(p : K)‖ ^ (r + h * k) ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r := by
    rw [pow_add, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
    exact pow_le_pow_of_le_one (norm_nonneg _) hp1 (Nat.le_mul_of_pos_left k hh0)
  calc ‖coeff n f‖ * ‖coeff N (α ^ n - β ^ n)‖
      ≤ ‖coeff n f‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r) :=
        mul_le_mul_of_nonneg_left (hpc.trans hkk) (norm_nonneg _)
    _ = (‖coeff n f‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ ^ r := by ring
    _ ≤ 1 * ‖(p : K)‖ ^ r := mul_le_mul_of_nonneg_right hk (pow_nonneg (norm_nonneg _) _)
    _ = ‖(p : K) ^ r‖ := by rw [one_mul, norm_pow]

end Norm

section Back

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma integralPS_trunc {a : PowerSeries K} (ha : IntegralPS a) (M : ℕ) :
    IntegralPS (trunc M a : PowerSeries K) := fun n => by
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs
  · exact ha n
  · simp

theorem bwd (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) [CharZero K]
    {p q : ℕ} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ) {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hfe : IsFunEqType p q σ f)
    {α β : PowerSeries K}
    (hα0 : constantCoeff α = 0) (hβ0 : constantCoeff β = 0) (hα : IntegralPS α)
    (hβ : IntegralPS β) {r : ℕ} (hr : 1 ≤ r)
    (hd : DivBy ((p : K) ^ r) (f.subst α - f.subst β)) :
    DivBy ((p : K) ^ r) (α - β) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [coeff_zero_eq_constantCoeff_apply, map_sub, hα0, hβ0, sub_zero, norm_zero]
    exact norm_nonneg _
  set c := coeff N (α - β) with hc
  have hc1 : ‖c‖ ≤ 1 := by
    rw [hc, map_sub]; exact (norm_sub_le_max' _ _).trans (max_le (hα N) (hβ N))
  set β₁ : PowerSeries K := β + C c * X ^ N with hβ₁
  have hcoeffβ₁ : ∀ n, coeff n β₁ = coeff n β + if n = N then c else 0 := by
    intro n
    rw [hβ₁, map_add, coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp
  have hβ₁0 : constantCoeff β₁ = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hcoeffβ₁, if_neg (by omega), add_zero,
      coeff_zero_eq_constantCoeff_apply, hβ0]
  have hβ₁i : IntegralPS β₁ := fun n => by
    rw [hcoeffβ₁]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hβ n) ?_)
    split_ifs
    · exact hc1
    · simp
  have hdt : DivBy ((p : K) ^ r)
      ((trunc (N + 1) α : PowerSeries K) - (trunc (N + 1) β₁ : PowerSeries K)) := by
    intro n
    rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_trunc, coeff_trunc]
    by_cases hn : n < N + 1
    · rw [if_pos hn, if_pos hn, hcoeffβ₁]
      by_cases hnN : n = N
      · subst hnN
        rw [if_pos rfl, hc, map_sub]
        simp
      · rw [if_neg hnN, add_zero, ← map_sub]
        exact ih n (by omega)
    · rw [if_neg hn, if_neg hn, sub_zero, norm_zero]; exact norm_nonneg _
  have hf := fwd h5 h6 hS hf0 hfe (constantCoeff_trunc_succ α hα0 N)
    (constantCoeff_trunc_succ β₁ hβ₁0 N) (integralPS_trunc hα _) (integralPS_trunc hβ₁i _) hr
    hdt N
  rw [map_sub, coeff_subst_trunc f α hα0, coeff_subst_trunc f β₁ hβ₁0] at hf
  have hkey := coeff_subst_add_C_mul_X_pow f β hβ0 c (N := N) hN
  rw [← hβ₁, hf1, one_mul] at hkey
  have hA := hd N
  rw [map_sub] at hA
  have : c = (coeff N (f.subst α) - coeff N (f.subst β)) -
      (coeff N (f.subst α) - coeff N (f.subst β₁)) := by rw [hkey]; ring
  rw [this]
  exact (norm_sub_le_max' _ _).trans (max_le hA hf)

end Back

theorem funEqCongr (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) :
    Formalism.G.FunEqCongr.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfe α β hα0 hβ0 hα hβ r hr
  exact ⟨fwd h5 h6 hS hf0 hfe hα0 hβ0 hα hβ hr, bwd h5 h6 hS hf0 hf1 hfe hα0 hβ0 hα hβ hr⟩

end Formalism.LT.CongrP

theorem Formalism.LT.FunEqCongr_of (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) :
    Formalism.G.FunEqCongr.{u} := Formalism.LT.CongrP.funEqCongr h5 h6
