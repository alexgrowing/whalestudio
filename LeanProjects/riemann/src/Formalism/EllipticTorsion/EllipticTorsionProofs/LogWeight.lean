import Mathlib
import Formalism.EllipticTorsion.UnitCancel
import Formalism.FormalGroupLog.LogDeterminesLaw

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.LogarithmWeight

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem norm_sum_mul_le {ι : Type*} (s : Finset ι) (f : ι → K) {w B : ℝ} (hw : 0 < w)
    (hB : 0 ≤ B) (h : ∀ i ∈ s, ‖f i‖ * w ≤ B) : ‖∑ i ∈ s, f i‖ * w ≤ B := by
  rw [← le_div_iff₀ hw]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hB hw.le)
  intro i hi
  rw [le_div_iff₀ hw]
  exact h i hi

theorem coeff_mul_le {f g : PowerSeries K} {c A B : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ n, ‖coeff n f‖ * c ^ n ≤ A) (hg : ∀ n, ‖coeff n g‖ * c ^ n ≤ B) (n : ℕ) :
    ‖coeff n (f * g)‖ * c ^ n ≤ A * B := by
  rw [PowerSeries.coeff_mul]
  apply norm_sum_mul_le _ _ (pow_pos hc n) (mul_nonneg hA hB)
  intro x hx
  have hx : x.1 + x.2 = n := by simpa using hx
  rw [norm_mul, ← hx, pow_add]
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ * (c ^ x.1 * c ^ x.2)
      = (‖coeff x.1 f‖ * c ^ x.1) * (‖coeff x.2 g‖ * c ^ x.2) := by ring
    _ ≤ A * B := mul_le_mul (hf _) (hg _) (by positivity) hA

theorem coeff_pow_le {f : PowerSeries K} {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hf : ∀ n, ‖coeff n f‖ * c ^ n ≤ A) (m n : ℕ) :
    ‖coeff n (f ^ m)‖ * c ^ n ≤ A ^ m := by
  induction m generalizing n with
  | zero =>
    rw [pow_zero, pow_zero]
    rcases n with _ | n
    · simp
    · simp [PowerSeries.coeff_one]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact coeff_mul_le hc (pow_nonneg hA _) hA ih hf n

theorem coeff_pow_of_cc {e : PowerSeries K} (he : constantCoeff e = 0) :
    ∃ g : PowerSeries K, constantCoeff g = coeff 1 e ∧
      ∀ m n : ℕ, coeff n (e ^ m) = if m ≤ n then coeff (n - m) (g ^ m) else 0 := by
  obtain ⟨g, hg⟩ := (PowerSeries.X_dvd_iff).mpr he
  refine ⟨g, ?_, fun m n => ?_⟩
  · rw [hg, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [hg, mul_pow, PowerSeries.coeff_X_pow_mul']

theorem coeff_pow_eq_zero {e : PowerSeries K} (he : constantCoeff e = 0) {m n : ℕ} (h : n < m) :
    coeff n (e ^ m) = 0 := by
  obtain ⟨g, -, hg⟩ := coeff_pow_of_cc he
  rw [hg, if_neg (by omega)]

theorem coeff_pow_self {e : PowerSeries K} (he : constantCoeff e = 0) (n : ℕ) :
    coeff n (e ^ n) = coeff 1 e ^ n := by
  obtain ⟨g, hg1, hg⟩ := coeff_pow_of_cc he
  rw [hg, if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hg1]

theorem coeff_subst_eq_sum {l e : PowerSeries K} (he : constantCoeff e = 0) (n : ℕ) :
    coeff n (l.subst e) = ∑ m ∈ Finset.range (n + 1), coeff m l * coeff n (e ^ m) := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' he)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) ?_]
  · simp [smul_eq_mul]
  · intro m hm
    simp only [Function.mem_support] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hm
    rw [coeff_pow_eq_zero he (by omega), smul_zero]

theorem subst_ga_eq {R : Type*} [CommRing R] (f : PowerSeries R) (hf0 : constantCoeff f = 0) :
    (FormalGroup.𝔾ₐ (R := R)).toPowerSeries.subst ![atX f, atY f] = atX f + atY f := by
  have hv := Formalism.G.LogP.hs2 (R := R) (u := atX f) (v := atY f)
    (PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0)
    (PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0)
  rw [FormalGroup.𝔾ₐ_toPowerSeries, MvPowerSeries.subst_add hv, MvPowerSeries.subst_X hv,
    MvPowerSeries.subst_X hv]
  rfl

theorem log_comp_hom [CharZero K] {F : FormalGroup K} {e l : PowerSeries K} (p : K) (hp : p ≠ 0)
    (he : IsHom F F e) (he1 : coeff 1 e = p) (hl : IsLog F l) :
    l.subst e = p • l := by
  have hlh : IsHom F FormalGroup.𝔾ₐ l := ((Formalism.G.log_iff_hom_additive K F l).mp hl).1
  have hh := Formalism.G.homComp_statement K F F FormalGroup.𝔾ₐ e l he hlh
  have h1 : coeff 1 (l.subst e) = p := by
    rw [coeff_subst_eq_sum he.1]
    simp [Finset.sum_range_succ, hl.2.1, he1]
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hg : IsLog F (p⁻¹ • l.subst e) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [hh.1]
    · rw [map_smul, h1, smul_eq_mul, inv_mul_cancel₀ hp]
    · simp only [atX, atY]
      rw [PowerSeries.subst_smul hF, hh.2, subst_ga_eq _ hh.1,
        PowerSeries.subst_smul (PowerSeries.HasSubst.X 0),
        PowerSeries.subst_smul (PowerSeries.HasSubst.X 1), smul_add]
  have := (Formalism.G.log_exists_unique K F).unique hg hl
  calc l.subst e = p • (p⁻¹ • l.subst e) := by rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
    _ = p • l := by rw [this]

end Formalism.ELL.LogarithmWeight

namespace Formalism.ELL

theorem logarithm_coeff_weight : Formalism.ELL.LogWeight := by
  intro K _ _ _ p q hp hp0 hp1 hq F e l he heI he1 he0 hl n hn
  set P : K := (p : K) with hPdef
  have hP0 : P ≠ 0 := norm_pos_iff.mp hp0
  have hle := Formalism.ELL.LogarithmWeight.log_comp_hom P hP0 he he1 hl
  have hq1 : (0:ℝ) < (q:ℝ) - 1 := by
    have : (2:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  set c : ℝ := ‖P‖ ^ (1 / ((q:ℝ) - 1)) with hc
  have cpos : 0 < c := Real.rpow_pos_of_pos hp0 _
  have cle : c ≤ 1 := Real.rpow_le_one (norm_nonneg _) hp1.le (div_nonneg zero_le_one hq1.le)
  have cpow : c ^ (q - 1) = ‖P‖ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_one, one_div, inv_mul_cancel₀ hq1.ne', Real.rpow_one]
  have cq : c ^ q = ‖P‖ * c := by
    rw [← cpow, ← pow_succ]
    congr 1
    omega
  have heB : ∀ d, ‖coeff d e‖ * c ^ d ≤ c ^ q := by
    intro d
    rcases Nat.lt_or_ge d q with hd | hd
    · rcases (show d = 0 ∨ d = 1 ∨ 2 ≤ d by omega) with rfl | rfl | hd2
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, he.1]
        simp only [norm_zero, zero_mul]
        positivity
      · rw [he1, pow_one, cq]
      · rw [he0 d hd2 hd]
        simp only [norm_zero, zero_mul]
        positivity
    · calc ‖coeff d e‖ * c ^ d ≤ 1 * c ^ d := by
            gcongr
            exact heI d
        _ = c ^ d := one_mul _
        _ ≤ c ^ q := pow_le_pow_of_le_one cpos.le cle hd
  have hpow : ∀ m k, ‖coeff k (e ^ m)‖ * c ^ k ≤ (c ^ q) ^ m :=
    Formalism.ELL.LogarithmWeight.coeff_pow_le cpos (by positivity) heB
  have hdiff : ∀ k, 2 ≤ k → ‖P‖ ≤ ‖P - P ^ k‖ := by
    intro k hk
    have hlt : ‖P ^ k‖ < ‖P‖ := by
      rw [norm_pow]
      exact pow_lt_self_of_lt_one₀ hp0 hp1 (by omega)
    have := IsUltrametricDist.norm_add_le_max (P - P ^ k) (P ^ k)
    rw [sub_add_cancel] at this
    rcases le_max_iff.mp this with h | h
    · exact h
    · exact absurd h (not_le.mpr hlt)
  have main : ∀ k, 1 ≤ k → ‖coeff k l‖ * c ^ k ≤ c := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
    · rw [hl.2.1]
      simp
    have hcoef := congrArg (coeff k) hle
    rw [Formalism.ELL.LogarithmWeight.coeff_subst_eq_sum he.1, Finset.sum_range_succ,
      Formalism.ELL.LogarithmWeight.coeff_pow_self he.1, he1, map_smul, smul_eq_mul] at hcoef
    have hS : coeff k l * (P - P ^ k) = ∑ m ∈ Finset.range k, coeff m l * coeff k (e ^ m) := by
      rw [mul_sub, mul_comm (coeff k l) P, ← hcoef]
      ring
    have hSb : ‖∑ m ∈ Finset.range k, coeff m l * coeff k (e ^ m)‖ * c ^ k ≤ c ^ q := by
      apply Formalism.ELL.LogarithmWeight.norm_sum_mul_le _ _ (pow_pos cpos k) (by positivity)
      intro m hm
      rw [Finset.mem_range] at hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl.1]
        simp only [zero_mul, norm_zero]
        positivity
      · have h1 := ih m hm hm0
        have h2 := hpow m k
        rw [norm_mul]
        have hqm : q + m ≤ 1 + q * m := by nlinarith
        have key : ‖coeff m l‖ * ‖coeff k (e ^ m)‖ * c ^ k * c ^ m ≤ c ^ q * c ^ m := by
          calc ‖coeff m l‖ * ‖coeff k (e ^ m)‖ * c ^ k * c ^ m
              = (‖coeff m l‖ * c ^ m) * (‖coeff k (e ^ m)‖ * c ^ k) := by ring
            _ ≤ c * (c ^ q) ^ m := mul_le_mul h1 h2 (by positivity) cpos.le
            _ = c ^ (1 + q * m) := by rw [← pow_mul, ← pow_succ', add_comm]
            _ ≤ c ^ (q + m) := pow_le_pow_of_le_one cpos.le cle hqm
            _ = c ^ q * c ^ m := pow_add _ _ _
        exact le_of_mul_le_mul_right key (pow_pos cpos m)
    have : ‖coeff k l‖ * c ^ k * ‖P‖ ≤ c * ‖P‖ := by
      calc ‖coeff k l‖ * c ^ k * ‖P‖ ≤ ‖coeff k l‖ * c ^ k * ‖P - P ^ k‖ := by
            gcongr
            exact hdiff k hk2
        _ = ‖coeff k l * (P - P ^ k)‖ * c ^ k := by rw [norm_mul]; ring
        _ ≤ c ^ q := by rw [hS]; exact hSb
        _ = c * ‖P‖ := by rw [cq, mul_comm]
    exact le_of_mul_le_mul_right this hp0
  have hm := main n hn
  have hcn : 0 < c ^ n := pow_pos cpos n
  have hfin : ‖coeff n l‖ ≤ c / c ^ n := by
    rw [le_div_iff₀ hcn]
    exact hm
  refine hfin.trans (le_of_eq ?_)
  rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_sub hp0]
  congr 1
  ring

end Formalism.ELL

end
