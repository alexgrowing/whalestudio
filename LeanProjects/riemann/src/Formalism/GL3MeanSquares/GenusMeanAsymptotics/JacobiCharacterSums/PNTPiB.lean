import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistC

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem abel_log (c : ℕ → ℝ) (h0 : c 0 = 0) (h1 : c 1 = 0) {X : ℝ} (hX : 2 ≤ X) :
    ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n = (∑ n ∈ Icc 0 ⌊X⌋₊, c n) / Real.log X +
      ∫ t in (2 : ℝ)..X, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2) := by
  rw [sum_mul_eq_sub_integral_mul₁ c (f := fun n ↦ (Real.log n)⁻¹) h0 h1,
    ← intervalIntegral.integral_of_le hX]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in (2 : ℝ)..X, deriv (fun x ↦ (Real.log x)⁻¹) u * f u =
        ∫ u in (2 : ℝ)..X, -(f u / (u * Real.log u ^ 2)) :=
      intervalIntegral.integral_congr fun u _ ↦ by simp [field]
    rw [int_deriv, intervalIntegral.integral_neg]
    ring
  · intro z ⟨_, _⟩
    have : z ≠ 0 := by linarith
    have : Real.log z ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨_, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop

theorem intervalIntegrable_sum_div (c : ℕ → ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2)) MeasureTheory.volume a b := by
  have hmeas : Measurable (fun t : ℝ => ∑ n ∈ Icc 0 ⌊t⌋₊, c n) :=
    (measurable_from_nat (f := fun m => ∑ n ∈ Icc 0 m, c n)).comp Nat.measurable_floor
  set B : ℝ := ∑ n ∈ Icc 0 ⌊b⌋₊, |c n| with hB
  have hbound : IntervalIntegrable (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, c n)) MeasureTheory.volume a b := by
    refine IntervalIntegrable.mono_fun' (f := fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n)) (g := fun _ => B)
      intervalIntegrable_const hmeas.aestronglyMeasurable ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have htb : t ≤ b := by
      have := ht.2
      simpa [max_eq_right hab] using this
    show ‖∑ n ∈ Icc 0 ⌊t⌋₊, c n‖ ≤ B
    rw [Real.norm_eq_abs]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono htb)) (fun _ _ _ => abs_nonneg _)
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Set.uIcc a b) := by
    have hpos : ∀ t ∈ Set.uIcc a b, 2 ≤ t := fun t ht => le_trans (le_trans ha (le_min le_rfl hab)) ht.1
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul continuousOn_id
      apply ContinuousOn.pow
      exact Real.continuousOn_log.mono (fun t ht => by simp; linarith [hpos t ht])
    · intro t ht
      have h2 := hpos t ht
      exact mul_ne_zero (by linarith) (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')
  have he : (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2)) =
      fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) * (1 / (t * Real.log t ^ 2)) := by
    funext t
    ring
  rw [he]
  exact hbound.mul_continuousOn hc

theorem intervalIntegrable_inv_log' {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have h1 : ∀ t ∈ Set.uIcc a b, 1 < t := fun t ht => lt_of_lt_of_le (lt_min ha hb) ht.1
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (lt_trans zero_lt_one (h1 t ht)))
  · intro t ht
    exact ne_of_gt (Real.log_pos (h1 t ht))

theorem integral_rpow_div_log {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    ∫ t in (2 : ℝ)..X, t ^ (β - 1) / Real.log t = liX (X ^ β) - liX ((2 : ℝ) ^ β) := by
  have h1X : 1 < X ^ β := Real.one_lt_rpow (by linarith) hβ
  have h12 : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  have hsub : liX (X ^ β) - liX ((2 : ℝ) ^ β) = ∫ u in ((2 : ℝ) ^ β)..(X ^ β), 1 / Real.log u := by
    unfold liX
    exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log' (by norm_num) h1X)
      (intervalIntegrable_inv_log' (by norm_num) h12)
  rw [hsub]
  have key := intervalIntegral.integral_comp_mul_deriv' (a := 2) (b := X) (f := fun t : ℝ => t ^ β)
    (f' := fun t : ℝ => β * t ^ (β - 1)) (g := fun u : ℝ => 1 / Real.log u) ?_ ?_ ?_
  · rw [← key]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    simp only [Function.comp]
    rw [Real.log_rpow ht0]
    field_simp
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    exact Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const t (β - 1) (Or.inl ht0))).continuousWithinAt
  · rintro u ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le hX] at ht
    have h1 : 1 < t ^ β := Real.one_lt_rpow (by linarith [ht.1]) hβ
    exact ((continuousAt_const).div (Real.continuousAt_log (by linarith)) (Real.log_pos h1).ne').continuousWithinAt

def Fm (K θ β t : ℝ) : ℝ := K * (t - θ * t ^ β / β)

theorem continuousOn_Fm_div_mul_log_sq (K θ β : ℝ) {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn (fun t => Fm K θ β t / (t * Real.log t ^ 2)) (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 2 ≤ t := fun t ht => le_trans ha ht.1
  apply ContinuousOn.div
  · unfold Fm
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub continuousOn_id
    apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl (by simp; linarith [hpos t ht]))
  · apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.pow
    exact Real.continuousOn_log.mono (fun t ht => by simp; linarith [hpos t ht])
  · intro t ht
    have h2 := hpos t ht
    exact mul_ne_zero (by linarith) (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')

theorem intervalIntegrable_Fm_div_mul_log_sq (K θ β : ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Fm K θ β t / (t * Real.log t ^ 2)) MeasureTheory.volume a b := by
  exact (continuousOn_Fm_div_mul_log_sq K θ β ha).intervalIntegrable_of_Icc hab

theorem Fm_parts (K θ : ℝ) {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    Fm K θ β X / Real.log X + ∫ t in (2 : ℝ)..X, Fm K θ β t / (t * Real.log t ^ 2) =
      Fm K θ β 2 / Real.log 2 + K * (liX X - θ * (liX (X ^ β) - liX ((2 : ℝ) ^ β))) := by
  have hder : ∀ t ∈ Set.uIcc 2 X, HasDerivAt (fun t => Fm K θ β t / Real.log t)
      (K * (1 / Real.log t) - K * θ * (t ^ (β - 1) / Real.log t) - Fm K θ β t / (t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : Real.log t ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    have hp : HasDerivAt (fun t : ℝ => t ^ β) (β * t ^ (β - 1)) t := Real.hasDerivAt_rpow_const (Or.inl h0)
    have hF : HasDerivAt (fun t => Fm K θ β t) (K * (1 - θ * (β * t ^ (β - 1)) / β)) t := by
      unfold Fm
      exact (((hasDerivAt_id t).sub ((hp.const_mul θ).div_const β)).const_mul K)
    have := hF.div (Real.hasDerivAt_log h0) h1
    have hβ0 : β ≠ 0 := hβ.ne'
    refine HasDerivAt.congr_deriv (f := fun t => Fm K θ β t / Real.log t) this ?_
    generalize Fm K θ β t = F
    field_simp
  have hi1 : IntervalIntegrable (fun t => K * (1 / Real.log t)) MeasureTheory.volume 2 X :=
    (intervalIntegrable_inv_log le_rfl hX).const_mul K
  have hi2' : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t) MeasureTheory.volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : Real.log t ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    exact ((Real.continuousAt_rpow_const t (β - 1) (Or.inl h0)).div (Real.continuousAt_log h0) h1).continuousWithinAt
  have hi2 := hi2'.const_mul (K * θ)
  have hi3 := intervalIntegrable_Fm_div_mul_log_sq K θ β le_rfl hX
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder ((hi1.sub hi2).sub hi3)
  rw [intervalIntegral.integral_sub (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow_div_log hβ hX] at hftc
  have hli : ∫ t in (2 : ℝ)..X, 1 / Real.log t = liX X := rfl
  rw [hli] at hftc
  linarith

theorem Fm_abs_le {K θ β t : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (ht : 1 ≤ t) : |Fm K θ β t| ≤ 3 * t := by
  have hb : 0 < β := by linarith
  have htb : t ^ β ≤ t := by
    have := Real.rpow_le_rpow_of_exponent_le ht hβ1
    rwa [Real.rpow_one] at this
  have htpos : 0 ≤ t ^ β := Real.rpow_nonneg (by linarith) _
  unfold Fm
  rw [abs_mul, abs_of_nonneg hK0]
  have h3 : |θ * t ^ β / β| ≤ 2 * t := by
    rw [abs_div, abs_mul, abs_of_nonneg htpos, abs_of_pos hb, div_le_iff₀ hb]
    nlinarith [mul_le_mul_of_nonneg_right hθ htpos, abs_nonneg θ]
  have h2 : |t - θ * t ^ β / β| ≤ 3 * t := by
    calc |t - θ * t ^ β / β| ≤ |t| + |θ * t ^ β / β| := abs_sub _ _
      _ ≤ t + 2 * t := by rw [abs_of_nonneg (by linarith)]; linarith
      _ = 3 * t := by ring
  calc K * |t - θ * t ^ β / β| ≤ 1 * (3 * t) := mul_le_mul hK1 h2 (abs_nonneg _) (by norm_num)
    _ = 3 * t := one_mul _

theorem liX_two_rpow_abs {β : ℝ} (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) : |liX ((2 : ℝ) ^ β)| ≤ 4 := by
  unfold liX
  have h1 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ β := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ
  have h2 : (2 : ℝ) ^ β ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
  have h3 : (1 : ℝ) < 2 ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 2) (b := (2 : ℝ) ^ β)
    (f := fun t => 1 / Real.log t) (C := 4) ?_
  · rw [Real.norm_eq_abs] at this
    calc _ ≤ 4 * |(2 : ℝ) ^ β - 2| := this
      _ ≤ 4 * 1 := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ = 4 := by norm_num
  · intro t ht
    rw [Set.uIoc_of_ge h2] at ht
    have hl : Real.log 2 / 2 ≤ Real.log t := by
      have : Real.log ((2 : ℝ) ^ (1 / 2 : ℝ)) ≤ Real.log t := Real.log_le_log (by positivity) (by linarith [ht.1])
      rw [Real.log_rpow (by norm_num)] at this; linarith
    have hl2 := Real.log_two_gt_d9
    have hl3 : 0 < Real.log t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hl3]
    linarith

theorem abel_core (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcΛ : ∀ n, c n ≤ ArithmeticFunction.vonMangoldt n)
    {K θ β D X : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hD : 0 ≤ D)
    (h : ∀ t, √X ≤ t → t ≤ X → |(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - Fm K θ β t| ≤ D * t) :
    |∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n - K * (liX X - θ * liX (X ^ β))| ≤
      5 * D * X / Real.log X + 40 * √X := by
  have h0 : c 0 = 0 := le_antisymm (by simpa using hcΛ 0) (hc0 0)
  have h1 : c 1 = 0 := le_antisymm (by simpa using hcΛ 1) (hc0 1)
  have hX2 : 2 ≤ X := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hs4 : 4 ≤ √X := by rw [Real.le_sqrt' (by norm_num)]; linarith
  have hss : √X * √X = X := Real.mul_self_sqrt (by linarith)
  have hsX : √X ≤ X := by nlinarith
  have hL : 1 ≤ Real.log X := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hX
    linarith
  have hL0 : 0 < Real.log X := by linarith
  have habel := abel_log c h0 h1 hX2
  have hparts := Fm_parts K θ (by linarith : 0 < β) hX2
  set Ψ : ℝ → ℝ := fun t => ∑ n ∈ Icc 0 ⌊t⌋₊, c n with hΨ
  set g : ℝ → ℝ := fun t => Ψ t / (t * Real.log t ^ 2) - Fm K θ β t / (t * Real.log t ^ 2) with hg
  have hgi : ∀ a b : ℝ, 2 ≤ a → a ≤ b → IntervalIntegrable g MeasureTheory.volume a b := fun a b ha hab =>
    (intervalIntegrable_sum_div c ha hab).sub (intervalIntegrable_Fm_div_mul_log_sq K θ β ha hab)
  have hI : ∫ t in (2 : ℝ)..X, g t = (∫ t in (2 : ℝ)..X, Ψ t / (t * Real.log t ^ 2)) -
      ∫ t in (2 : ℝ)..X, Fm K θ β t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_sub (intervalIntegrable_sum_div c le_rfl hX2) (intervalIntegrable_Fm_div_mul_log_sq K θ β le_rfl hX2)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgi 2 (√X) le_rfl (by linarith))
    (hgi (√X) X (by linarith) hsX)
  have hΨle : ∀ t : ℝ, 0 ≤ t → |Ψ t| ≤ 6 * t := by
    intro t ht
    have hn : 0 ≤ Ψ t := Finset.sum_nonneg (fun n _ => hc0 n)
    rw [abs_of_nonneg hn]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    calc Ψ t ≤ ∑ n ∈ Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n := Finset.sum_le_sum (fun n _ => hcΛ n)
      _ = Chebyshev.psi t := (Chebyshev.psi_eq_sum_Icc t).symm
      _ ≤ (Real.log 4 + 4) * t := Chebyshev.psi_le_const_mul_self ht
      _ ≤ 6 * t := by gcongr; linarith
  have hI1 : |∫ t in (2 : ℝ)..√X, g t| ≤ 36 * |√X - 2| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have ht2 : 2 < t := ht.1
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2.le
    have hsq : 1 / 4 ≤ Real.log t ^ 2 := by nlinarith
    have hpos : 0 < t * Real.log t ^ 2 := by positivity
    have ha := hΨle t (by linarith)
    have hb := Fm_abs_le hK0 hK1 hθ hβ hβ1 (by linarith : 1 ≤ t)
    rw [Real.norm_eq_abs, hg]
    simp only []
    rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hab : |Ψ t - Fm K θ β t| ≤ 9 * t := by
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    nlinarith
  have hI2 : |∫ t in (√X)..X, g t| ≤ 4 * D / Real.log X ^ 2 * |X - √X| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hsX] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt : Real.log X / 2 ≤ Real.log t := by
      rw [← Real.log_sqrt (by linarith)]
      exact Real.log_le_log (by linarith) ht.1.le
    have hlt0 : 0 < Real.log t := by linarith
    have hsq : Real.log X ^ 2 ≤ 4 * Real.log t ^ 2 := by nlinarith
    have hpos : 0 < t * Real.log t ^ 2 := by positivity
    rw [Real.norm_eq_abs, hg]
    simp only []
    rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc |Ψ t - Fm K θ β t| * Real.log X ^ 2 ≤ (D * t) * (4 * Real.log t ^ 2) := by
          gcongr
          exact h t ht.1.le ht.2
      _ = 4 * D * (t * Real.log t ^ 2) := by ring
  have heq : ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n - K * (liX X - θ * liX (X ^ β)) =
      (Ψ X - Fm K θ β X) / Real.log X + ((∫ t in (2 : ℝ)..√X, g t) + ∫ t in (√X)..X, g t) +
        Fm K θ β 2 / Real.log 2 + K * θ * liX ((2 : ℝ) ^ β) := by
    have e1 : K * (liX X - θ * (liX (X ^ β) - liX ((2 : ℝ) ^ β))) =
        K * (liX X - θ * liX (X ^ β)) + K * θ * liX ((2 : ℝ) ^ β) := by ring
    have e2 : (Ψ X - Fm K θ β X) / Real.log X = Ψ X / Real.log X - Fm K θ β X / Real.log X := sub_div _ _ _
    linarith [habel, hparts, hI, hsplit]
  have b1 : |(Ψ X - Fm K θ β X) / Real.log X| ≤ D * X / Real.log X := by
    rw [abs_div, abs_of_pos hL0]
    gcongr
    exact h X hsX le_rfl
  have b2 : |Fm K θ β 2 / Real.log 2| ≤ 12 := by
    have := Fm_abs_le hK0 hK1 hθ hβ hβ1 (by norm_num : (1 : ℝ) ≤ 2)
    rw [abs_div, abs_of_pos (by linarith : 0 < Real.log 2), div_le_iff₀ (by linarith)]
    linarith
  have b3 : |K * θ * liX ((2 : ℝ) ^ β)| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hK0]
    calc K * |θ| * |liX ((2 : ℝ) ^ β)| ≤ 1 * 1 * 4 := by
          gcongr
          exact liX_two_rpow_abs hβ hβ1
      _ = 4 := by norm_num
  have b4 : 4 * D / Real.log X ^ 2 * |X - √X| ≤ 4 * (D * X / Real.log X) := by
    rw [abs_of_nonneg (by linarith)]
    have hDX : 0 ≤ D * X := by positivity
    have : D * X / Real.log X ^ 2 ≤ D * X / Real.log X := by
      apply div_le_div_of_nonneg_left hDX hL0
      nlinarith
    calc 4 * D / Real.log X ^ 2 * (X - √X) ≤ 4 * D / Real.log X ^ 2 * X := by
          gcongr
          linarith
      _ = 4 * (D * X / Real.log X ^ 2) := by ring
      _ ≤ _ := by linarith
  have b5 : 36 * |√X - 2| ≤ 36 * √X - 72 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  rw [heq]
  have e5 : 5 * D * X / Real.log X = 5 * (D * X / Real.log X) := by ring
  rw [e5]
  rw [abs_le] at *
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, hI1.1, hI1.2, hI2.1, hI2.2]

end Formalism.HermitianLattices.Ext.PrimesInProgressions
