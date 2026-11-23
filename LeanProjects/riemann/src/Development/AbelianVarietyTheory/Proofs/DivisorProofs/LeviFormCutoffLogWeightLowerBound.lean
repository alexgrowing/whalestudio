import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeightLevi

open Complex ComplexConjugate Filter

theorem deriv_zero_of_eqOn {χ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {c : ℝ}
    (h : ∀ s ∈ U, χ s = c) : ∀ s ∈ U, deriv χ s = 0 ∧ deriv (deriv χ) s = 0 := by
  have h1 : ∀ s ∈ U, deriv χ s = 0 := fun s hs => by
    have e : χ =ᶠ[𝓝 s] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hs) h
    rw [e.deriv_eq]; simp
  intro s hs
  refine ⟨h1 s hs, ?_⟩
  have e : deriv χ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := Filter.eventually_of_mem (hU.mem_nhds hs) h1
  rw [e.deriv_eq]; simp

theorem hasDerivAt_logShift {δ s : ℝ} (hs : 0 < s + δ) :
    HasDerivAt (fun s => Real.log ((s + δ) / 2)) (s + δ)⁻¹ s := by
  have h1 : HasDerivAt (fun s : ℝ => (s + δ) / 2) (1 / 2) s :=
    ((hasDerivAt_id' s).add_const δ).div_const 2
  convert h1.log (by positivity) using 1
  field_simp

theorem hasDerivAt_cutLog {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {δ s : ℝ} (hs : 0 < s + δ) :
    HasDerivAt (fun s => χ s * Real.log ((s + δ) / 2))
      (deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹) s := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  exact (hd s).hasDerivAt.mul (hasDerivAt_logShift hs)

theorem derivs_cutLog {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {δ t : ℝ} (ht : 0 < t + δ) :
    deriv (fun s => χ s * Real.log ((s + δ) / 2)) t =
        deriv χ t * Real.log ((t + δ) / 2) + χ t * (t + δ)⁻¹ ∧
      deriv (deriv (fun s => χ s * Real.log ((s + δ) / 2))) t =
        deriv (deriv χ) t * Real.log ((t + δ) / 2) + 2 * deriv χ t * (t + δ)⁻¹ -
          χ t * ((t + δ)⁻¹) ^ 2 := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hd2 : Differentiable ℝ (deriv χ) :=
    (contDiff_infty_iff_deriv.1 hχ).2.differentiable (by simp)
  have hU : Set.Ioi (-δ) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have e : deriv (fun s => χ s * Real.log ((s + δ) / 2)) =ᶠ[𝓝 t]
      fun s => deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹ :=
    Filter.eventually_of_mem hU fun s hs =>
      (hasDerivAt_cutLog hχ (by simp only [Set.mem_Ioi] at hs; linarith)).deriv
  refine ⟨(hasDerivAt_cutLog hχ ht).deriv, ?_⟩
  rw [e.deriv_eq]
  have hinv : HasDerivAt (fun s => (s + δ)⁻¹) (-1 / (t + δ) ^ 2) t :=
    ((hasDerivAt_id' t).add_const δ).inv ht.ne'
  have h : HasDerivAt (fun s => deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹) _ t :=
    ((hd2 t).hasDerivAt.mul (hasDerivAt_logShift ht)).add ((hd t).hasDerivAt.mul hinv)
  rw [h.deriv]
  field_simp
  ring

theorem cutLog_bounds (χ : ℝ → ℝ) (A : ℝ) (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (h1 : ∀ t, t ≤ 1 / 4 → χ t = 1) (h0 : ∀ t, 1 ≤ t → χ t = 0) (hA1 : ∀ t, |deriv χ t| ≤ A)
    (hA2 : ∀ t, |deriv (deriv χ) t| ≤ A) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    -(13 * A + 20) ≤ deriv (fun s => χ s * Real.log ((s + δ) / 2)) t ∧
      -(13 * A + 20) ≤ deriv (fun s => χ s * Real.log ((s + δ) / 2)) t +
        t * deriv (deriv (fun s => χ s * Real.log ((s + δ) / 2))) t := by
  have htd : 0 < t + δ := by linarith
  obtain ⟨e1, e2⟩ := derivs_cutLog hχ htd
  rw [e1, e2]
  have hA : 0 ≤ A := (abs_nonneg _).trans (hA1 0)
  set L := Real.log ((t + δ) / 2)
  set u := (t + δ)⁻¹ with hu_def
  have hu : 0 < u := inv_pos.2 htd
  have htu : t * u ≤ 1 := by
    rw [hu_def, ← div_eq_mul_inv, div_le_one htd]; linarith
  have htu0 : 0 ≤ t * u := mul_nonneg ht hu.le
  have hc0 := h01 t
  have hpos : 0 ≤ χ t * u * (1 - t * u) :=
    mul_nonneg (mul_nonneg hc0.1 hu.le) (by linarith)
  have hexp : deriv χ t * L + χ t * u + t * (deriv (deriv χ) t * L + 2 * deriv χ t * u - χ t * u ^ 2) =
      deriv χ t * L + t * (deriv (deriv χ) t * L) + 2 * (deriv χ t * (t * u)) +
        χ t * u * (1 - t * u) := by ring
  rw [hexp]
  by_cases hc : t < 1 / 4 ∨ 1 < t
  · have hz : deriv χ t = 0 ∧ deriv (deriv χ) t = 0 := by
      rcases hc with hc | hc
      · exact deriv_zero_of_eqOn isOpen_Iio (fun s hs => h1 s (le_of_lt hs)) t hc
      · exact deriv_zero_of_eqOn isOpen_Ioi (fun s hs => h0 s (le_of_lt hs)) t hc
    rw [hz.1, hz.2]
    have : 0 ≤ χ t * u := mul_nonneg hc0.1 hu.le
    constructor <;> nlinarith
  · push_neg at hc
    have hx1 : (t + δ) / 2 ≤ 1 := by linarith
    have hx0 : 1 / 8 ≤ (t + δ) / 2 := by linarith
    have hL0 : L ≤ 0 := Real.log_nonpos (by linarith) hx1
    have hl8 : Real.log (1 / 8) = -(3 * Real.log 2) := by
      rw [show (1 : ℝ) / 8 = ((2 : ℝ) ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
    have hL1 : -3 ≤ L := by
      have := Real.log_le_log (by norm_num) hx0
      have := Real.log_two_lt_d9
      linarith
    have hLabs : |L| ≤ 3 := abs_le.2 ⟨hL1, by linarith⟩
    have b1 : -(3 * A) ≤ deriv χ t * L := by
      have : |deriv χ t * L| ≤ A * 3 := by
        rw [abs_mul]; exact mul_le_mul (hA1 t) hLabs (abs_nonneg _) hA
      linarith [neg_abs_le (deriv χ t * L)]
    have b2 : -(3 * A) ≤ t * (deriv (deriv χ) t * L) := by
      have : |t * (deriv (deriv χ) t * L)| ≤ 1 * (A * 3) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht]
        exact mul_le_mul (by linarith) (mul_le_mul (hA2 t) hLabs (abs_nonneg _) hA)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
      linarith [neg_abs_le (t * (deriv (deriv χ) t * L))]
    have b3 : -A ≤ deriv χ t * (t * u) := by
      have : |deriv χ t * (t * u)| ≤ A * 1 := by
        rw [abs_mul, abs_of_nonneg htu0]
        exact mul_le_mul (hA1 t) htu htu0 hA
      linarith [neg_abs_le (deriv χ t * (t * u))]
    have : 0 ≤ χ t * u := mul_nonneg hc0.1 hu.le
    constructor <;> nlinarith

theorem normSq_sum_conj_mul_le {n : ℕ} (a b : Fin n → ℂ) :
    Complex.normSq (∑ m, conj (a m) * b m) ≤
      (∑ m, Complex.normSq (a m)) * ∑ m, Complex.normSq (b m) := by
  have h1 : ‖∑ m, conj (a m) * b m‖ ≤ ∑ m, ‖a m‖ * ‖b m‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ => by
      rw [norm_mul, Complex.norm_conj]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun m => ‖a m‖) (fun m => ‖b m‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ m, conj (a m) * b m‖ ^ 2 ≤ (∑ m, ‖a m‖ * ‖b m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem levi_cutLog_lower : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) →
    (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) →
    (∀ t, |deriv (deriv χ) t| ≤ A) → ∀ (n : ℕ) (ρ δ : ℝ), 0 < ρ → 0 < δ → δ ≤ 1 →
    ∀ (z : V n) (ξ : Fin n → ℂ), -((13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) ≤
      (leviV n (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ))
        z ξ).re := by
  intro χ A hχ h01 h1 h0 hA1 hA2 n ρ δ hρ hδ hδ1 z ξ
  set k : ℝ → ℝ := fun s => χ s * Real.log ((s + δ) / 2) with hk
  let L : Fin n → V n →L[ℂ] ℂ := fun j => ((ρ : ℂ)⁻¹) • EuclideanSpace.proj j
  have hLapp : ∀ j y, L j y = (ρ : ℂ)⁻¹ * y j := fun j y => by simp [L]
  set v : V n → ℝ := fun y => ∑ j, Complex.normSq (L j y) with hvdef
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hv : ∀ y : V n, ‖y‖ ^ 2 / ρ ^ 2 = v y := by
    intro y
    simp only [hvdef, hLapp, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal,
      EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    field_simp
  have hfun : (fun w : V n => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ))
      = fun w => ((k (v w) : ℝ) : ℂ) := by
    funext w; rw [hv w]
  rw [hfun]
  have hLc : ∀ j, ContDiffAt ℂ 2 (fun y => L j y) z := fun j => (L j).contDiff.contDiffAt
  have hu : ∀ j, ContDiffAt ℝ 2 (fun y => Complex.normSq (L j y)) z := fun j =>
    H.contDiffAt_normSq_comp (hLc j)
  have hvC : ContDiffAt ℝ 2 v z := ContDiffAt.sum fun j _ => hu j
  have ht0 : 0 ≤ v z := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hkC : ContDiffAt ℝ 2 k (v z) := by
    have hχ2 : ContDiffAt ℝ 2 χ (v z) := hχ.contDiffAt.of_le (by norm_cast)
    exact hχ2.mul (((contDiffAt_id.add contDiffAt_const).div_const (2 : ℝ)).log
      (by simp only [id]; positivity))
  rw [H.leviChain n k v z ξ hvC hkC]
  have hwdL : ∀ j m, wd n m (fun y => L j y) z = (ρ : ℂ)⁻¹ * (if j = m then 1 else 0) := by
    intro j m
    rw [wd_of_differentiableAt (L j).differentiableAt, (L j).fderiv, hLapp]
    simp [bas, EuclideanSpace.single_apply]
  have hLevi : leviV n (fun y => ((v y : ℝ) : ℂ)) z ξ =
      ((∑ j, Complex.normSq ((ρ : ℂ)⁻¹ * ξ j) : ℝ) : ℂ) := by
    rw [show (fun y => ((v y : ℝ) : ℂ)) = fun y => ((∑ j, Complex.normSq (L j y) : ℝ) : ℂ) from rfl,
      H.leviV_ofReal_sum hu, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.leviV_normSq_comp (hLc j)]
    simp [hwdL]
  have hwd : ∀ m, wd n m (fun y => ((v y : ℝ) : ℂ)) z = (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) := by
    intro m
    rw [show (fun y => ((v y : ℝ) : ℂ)) = fun y => ((∑ j, Complex.normSq (L j y) : ℝ) : ℂ) from rfl,
      H.wd_ofReal_sum (fun j => (hu j).differentiableAt (by simp))]
    refine (Finset.sum_congr rfl fun j _ => by rw [H.wd_normSq_comp (hLc j), hwdL]).trans ?_
    simp [hLapp]
  rw [hLevi]
  simp only [hwd]
  set P := ∑ j, Complex.normSq ((ρ : ℂ)⁻¹ * ξ j) with hP
  set N := Complex.normSq (∑ m, (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) * ξ m) with hN
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hNt : N ≤ v z * P := by
    have e : ∑ m, (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) * ξ m =
        ∑ m, conj ((ρ : ℂ)⁻¹ * z m) * ((ρ : ℂ)⁻¹ * ξ m) :=
      Finset.sum_congr rfl fun m _ => by ring
    have ev : v z = ∑ m, Complex.normSq ((ρ : ℂ)⁻¹ * z m) :=
      Finset.sum_congr rfl fun m _ => by rw [hLapp]
    rw [hN, e, ev, hP]
    exact normSq_sum_conj_mul_le _ _
  have hPe : (13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 = (13 * A + 20) * P := by
    rw [hP, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    field_simp
  rw [hPe]
  obtain ⟨b1, b2⟩ := cutLog_bounds χ A hχ h01 h1 h0 hA1 hA2 hδ hδ1 ht0
  by_cases hs : 0 ≤ deriv (deriv k) (v z)
  · have := mul_le_mul_of_nonneg_right b1 hP0
    have := mul_nonneg hs hN0
    nlinarith
  · push_neg at hs
    have h3 : deriv (deriv k) (v z) * (v z * P) ≤ deriv (deriv k) (v z) * N :=
      mul_le_mul_of_nonpos_left hNt hs.le
    have := mul_le_mul_of_nonneg_right b2 hP0
    nlinarith

end GlobalTheory.PeakWeightLevi
