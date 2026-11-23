import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegRadialWeight
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionCluster
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegLelongAnnulus

section Chart

variable {n m : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin m) (Fin n) ℂ}

theorem maDens_congr_germ {F G : Fin m → (Fin m → ℂ) → ℝ} {y : Fin m → ℂ}
    (h : ∀ k, F k =ᶠ[𝓝 y] G k) : ReciprocityTheory.AnForm.maDens F y = ReciprocityTheory.AnForm.maDens G y := by
  have h2 : ∀ k, fderiv ℝ (fderiv ℝ (F k)) y = fderiv ℝ (fderiv ℝ (G k)) y :=
    fun k => ((h k).fderiv (𝕜 := ℝ)).fderiv_eq
  have h3 : (fun k => ReciprocityTheory.AnForm.hessC (F k) y) = fun k => ReciprocityTheory.AnForm.hessC (G k) y := by
    funext k
    ext i j
    dsimp only [ReciprocityTheory.AnForm.hessC]
    rw [h2 k]
  unfold ReciprocityTheory.AnForm.maDens
  rw [h3]

theorem abs_chartDens_le (hA : IsFiniteProjection J A) {w f : (Fin n → ℂ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ z, |w z| ≤ C * f z) (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    |chartDens J A w φ y| ≤ C * chartAbsDens J A f φ y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
  split_ifs with h
  · beta_reduce
    rw [abs_mul, abs_mul]
    calc |w z| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y|
        ≤ (C * |f z|) * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y| :=
          mul_le_mul_of_nonneg_right ((hw z).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC))
            (abs_nonneg _)
      _ = C * (|f z| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y|) := by ring
  · simp

theorem tendsto_chartDens (hA : IsFiniteProjection J A) {w : ℕ → (Fin n → ℂ) → ℝ} {w' : (Fin n → ℂ) → ℝ}
    (hw : ∀ z, Tendsto (fun k => w k z) atTop (𝓝 (w' z))) (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    Tendsto (fun k => chartDens J A (w k) φ y) atTop (𝓝 (chartDens J A w' φ y)) := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine tendsto_finsetSum _ fun z _ => ?_
  split_ifs with h
  · exact (hw z).mul_const _
  · exact tendsto_const_nhds

theorem chartDens_congr_fun {w : (Fin n → ℂ) → ℝ} {φ φ' : Fin m → (Fin n → ℂ) → ℝ}
    (hloc : ∀ z ∈ zeroSet J, w z ≠ 0 → ∀ k, φ k =ᶠ[𝓝 z] φ' k) (y : Fin m → ℂ) :
    chartDens J A w φ y = chartDens J A w φ' y := by
  unfold chartDens sheetSum
  refine finsum_congr fun z => finsum_congr fun hz => ?_
  split_ifs with h
  · beta_reduce
    by_cases hw : w z = 0
    · rw [hw, zero_mul, zero_mul]
    · obtain ⟨U, hU, hAz, hdiff, hsz, -, -⟩ := h.choose_spec
      have hcont : ContinuousAt h.choose (A *ᵥ z) :=
        (hdiff.differentiableAt (hU.mem_nhds hAz)).continuousAt
      have hy : A *ᵥ z = y := hz.2
      rw [← hy]
      refine congrArg (w z * ·) (maDens_congr_germ fun k => ?_)
      have hk := hloc z hz.1 hw k
      rw [← hsz] at hk
      exact hcont.eventually hk
  · rfl

theorem chartDens_sub' (hA : IsFiniteProjection J A) (c₁ c₂ : ℝ) (w₁ w₂ : (Fin n → ℂ) → ℝ)
    (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    chartDens J A (fun z => c₁ * w₁ z - c₂ * w₂ z) φ y =
      c₁ * chartDens J A w₁ φ y - c₂ * chartDens J A w₂ φ y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> ring

theorem chartDens_const_mul (hA : IsFiniteProjection J A) (c : ℝ) (w : (Fin n → ℂ) → ℝ)
    (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    chartDens J A (fun z => c * w z) φ y = c * chartDens J A w φ y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> ring

variable (hCM : ChartMassCompact.Statement) (hJ : J.IsPrime)
  (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (m : ℕ)) (hA : IsFiniteProjection J A)
include hCM hJ hdim hA

theorem integrable_chartDens {φ : Fin m → (Fin n → ℂ) → ℝ} (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    {f : (Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {C : ℝ} (hC : 0 ≤ C)
    {w : (Fin n → ℂ) → ℝ} (hwm : Measurable w) (hb : ∀ z, |w z| ≤ C * f z) :
    Integrable (chartDens J A w φ) :=
  ((hCM n m J A f φ hJ hdim hA hf.continuousOn hφ (Or.inl hfc)).const_mul C).mono'
    (SheetSumMeasurable.proof n m J A w φ hJ hdim hA hwm hφ).1.aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_chartDens_le hA hC hb φ y)

theorem tendsto_integral_chartDens {φ : Fin m → (Fin n → ℂ) → ℝ} (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    {f : (Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {C : ℝ} (hC : 0 ≤ C)
    {w : ℕ → (Fin n → ℂ) → ℝ} {w' : (Fin n → ℂ) → ℝ} (hwm : ∀ k, Measurable (w k))
    (hb : ∀ k z, |w k z| ≤ C * f z) (hw : ∀ z, Tendsto (fun k => w k z) atTop (𝓝 (w' z))) :
    Tendsto (fun k => ∫ y, chartDens J A (w k) φ y) atTop (𝓝 (∫ y, chartDens J A w' φ y)) :=
  tendsto_integral_of_dominated_convergence (fun y => C * chartAbsDens J A f φ y)
    (fun k => (SheetSumMeasurable.proof n m J A (w k) φ hJ hdim hA (hwm k) hφ).1.aestronglyMeasurable)
    ((hCM n m J A f φ hJ hdim hA hf.continuousOn hφ (Or.inl hfc)).const_mul C)
    (fun k => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_chartDens_le hA hC (hb k) φ y)
    (Eventually.of_forall fun y => tendsto_chartDens hA hw φ y)

end Chart

section Radial

theorem continuous_kernel (e : ℕ) : Continuous fun τ : ℝ => ((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1) :=
  continuous_const.mul (continuous_pow _)

theorem kernel_nonneg (e : ℕ) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ ((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1) := by
  positivity

theorem integral_comp_div_sq (e : ℕ) (h : ℝ → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) :
    ∫ τ in (0 : ℝ)..t, h (τ / ρ ^ 2) * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ρ ^ (2 * (e + 1)) * ∫ w in (0 : ℝ)..t / ρ ^ 2, h w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) := by
  have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun w => h w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) := ⟨_, rfl⟩
  have key : ∀ τ : ℝ, h (τ / ρ ^ 2) * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ρ ^ (2 * e) * G (τ / ρ ^ 2) := by
    intro τ
    rw [hG]
    simp only [Nat.add_sub_cancel]
    rw [div_pow, ← pow_mul]
    field_simp
  have key2 : ∀ w : ℝ, h w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) = G w := fun w => by rw [hG]
  simp only [key, key2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div G hρ2, zero_div, smul_eq_mul]
  ring

theorem radialTransform_comp_div (e : ℕ) (h : ℝ → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) :
    radialTransform (e + 1) (fun τ => h (τ / ρ ^ 2)) t =
      ρ ^ (2 * (e + 1)) * radialTransform (e + 1) h (t / ρ ^ 2) := by
  unfold radialTransform
  beta_reduce
  rw [integral_comp_div_sq e h hρ t]
  have ht : t ^ (e + 1) = ρ ^ (2 * (e + 1)) * (t / ρ ^ 2) ^ (e + 1) := by
    rw [div_pow, ← pow_mul]
    field_simp
  rw [ht]
  ring

theorem radialTransform_sub (e : ℕ) {f₁ f₂ : ℝ → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (c₁ c₂ t : ℝ) :
    radialTransform (e + 1) (fun τ => c₁ * f₁ τ - c₂ * f₂ τ) t =
      c₁ * radialTransform (e + 1) f₁ t - c₂ * radialTransform (e + 1) f₂ t := by
  unfold radialTransform
  beta_reduce
  have e1 : ∀ τ : ℝ, (c₁ * f₁ τ - c₂ * f₂ τ) * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      c₁ * (f₁ τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) -
        c₂ * (f₂ τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) := fun τ => by ring
  simp only [e1]
  rw [intervalIntegral.integral_sub (f := fun τ => c₁ * (f₁ τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))))
      (g := fun τ => c₂ * (f₂ τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))))
      ((continuous_const.mul (h₁.mul (continuous_kernel e))).intervalIntegrable _ _)
      ((continuous_const.mul (h₂.mul (continuous_kernel e))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

theorem continuous_radialTransform (e : ℕ) {h : ℝ → ℝ} (hc : Continuous h) :
    Continuous (radialTransform (e + 1) h) := by
  unfold radialTransform
  exact (hc.mul (continuous_pow _)).sub (intervalIntegral.continuous_primitive
    (fun a b => (hc.mul (continuous_kernel e)).intervalIntegrable a b) 0)

def pk (k : ℕ) : ℝ := 1 - 1 / ((k : ℝ) + 1) / 2

def qk (k : ℕ) : ℝ := 1 - 1 / ((k : ℝ) + 1) / 4

theorem inv_succ_pos (k : ℕ) : 0 < 1 / ((k : ℝ) + 1) := by positivity

theorem inv_succ_le_one (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 :=
  (div_le_one (by positivity)).2 (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])

theorem half_le_pk (k : ℕ) : 1 / 2 ≤ pk k := by
  have := inv_succ_le_one k
  unfold pk
  linarith

theorem pk_pos (k : ℕ) : 0 < pk k := lt_of_lt_of_le (by norm_num) (half_le_pk k)

theorem pk_lt_qk (k : ℕ) : pk k < qk k := by
  have := inv_succ_pos k
  unfold pk qk
  linarith

theorem qk_lt_one (k : ℕ) : qk k < 1 := by
  have := inv_succ_pos k
  unfold qk
  linarith

theorem pk_le_one (k : ℕ) : pk k ≤ 1 := ((pk_lt_qk k).trans (qk_lt_one k)).le

theorem tendsto_pk : Tendsto pk atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2)
  rw [zero_div, sub_zero] at h
  exact h

def hk (k : ℕ) : ContDiffBump (0 : ℝ) := ⟨pk k, qk k, pk_pos k, pk_lt_qk k⟩

theorem hk_one {k : ℕ} {v : ℝ} (h0 : 0 ≤ v) (hv : v ≤ pk k) : hk k v = 1 :=
  (hk k).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg h0]
    exact hv)

theorem hk_zero {k : ℕ} {v : ℝ} (hv : qk k ≤ v) : hk k v = 0 :=
  (hk k).zero_of_le_dist (by
    rw [Real.dist_eq, sub_zero]
    exact hv.trans (le_abs_self v))

theorem hk_zero_of_one_le {k : ℕ} {v : ℝ} (hv : 1 ≤ v) : hk k v = 0 :=
  hk_zero ((qk_lt_one k).le.trans hv)

def Ik (e k : ℕ) : ℝ := ∫ w in (0 : ℝ)..1, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1))

theorem continuous_hk_kernel (e k : ℕ) :
    Continuous fun w : ℝ => hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) :=
  (hk k).continuous.mul (continuous_kernel e)

theorem integral_hk_of_one_le (e k : ℕ) {v : ℝ} (hv : 1 ≤ v) :
    ∫ w in (0 : ℝ)..v, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) = Ik e k := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    ((continuous_hk_kernel e k).intervalIntegrable _ _) ((continuous_hk_kernel e k).intervalIntegrable _ _)]
  have h0 : ∫ w in (1 : ℝ)..v, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun w hw => ?_]
    · simp
    · rw [Set.uIcc_of_le hv] at hw
      simp only
      rw [hk_zero_of_one_le hw.1, zero_mul]
  rw [h0, add_zero, Ik]

theorem radialTransform_hk_of_le (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) (hv : v ≤ pk k) :
    radialTransform (e + 1) (hk k) v = 0 :=
  radialTransform_eq_zero_of_const e (hk k) (t₀ := pk k)
    (fun τ hτ => by rw [hk_one hτ.1 hτ.2, hk_one le_rfl (pk_pos k).le]) ⟨h0, hv⟩

theorem radialTransform_hk_of_one_le (e k : ℕ) {v : ℝ} (hv : 1 ≤ v) :
    radialTransform (e + 1) (hk k) v = -Ik e k := by
  unfold radialTransform
  rw [hk_zero_of_one_le hv, zero_mul, integral_hk_of_one_le e k hv, zero_sub]

theorem integral_kernel (e : ℕ) (t : ℝ) :
    ∫ w in (0 : ℝ)..t, 1 * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) = t ^ (e + 1) := by
  rw [integral_const_mul_dpow, one_mul]

theorem integral_hk_le (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) :
    ∫ w in (0 : ℝ)..v, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) ≤ v ^ (e + 1) := by
  rw [← integral_kernel e v]
  exact intervalIntegral.integral_mono_on h0 ((continuous_hk_kernel e k).intervalIntegrable _ _)
    ((continuous_const.mul (continuous_kernel e)).intervalIntegrable _ _)
    fun w hw => mul_le_mul_of_nonneg_right (hk k).le_one (kernel_nonneg e hw.1)

theorem integral_hk_nonneg (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) :
    0 ≤ ∫ w in (0 : ℝ)..v, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) :=
  intervalIntegral.integral_nonneg h0 fun _ hw => mul_nonneg (hk k).nonneg (kernel_nonneg e hw.1)

theorem Ik_le_one (e k : ℕ) : Ik e k ≤ 1 := by
  have := integral_hk_le e k zero_le_one
  rw [one_pow] at this
  exact this

theorem pk_pow_le_Ik (e k : ℕ) : pk k ^ (e + 1) ≤ Ik e k := by
  unfold Ik
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := pk k)
    ((continuous_hk_kernel e k).intervalIntegrable _ _) ((continuous_hk_kernel e k).intervalIntegrable _ _)]
  have h1 : ∫ w in (0 : ℝ)..pk k, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) = pk k ^ (e + 1) := by
    rw [← integral_kernel e (pk k)]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (pk_pos k).le] at hw
    rw [hk_one hw.1 hw.2]
  have h2 : 0 ≤ ∫ w in pk k..1, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) :=
    intervalIntegral.integral_nonneg (pk_le_one k)
      fun w hw => mul_nonneg (hk k).nonneg (kernel_nonneg e ((pk_pos k).le.trans hw.1))
  linarith

theorem Ik_nonneg (e k : ℕ) : 0 ≤ Ik e k := (pow_nonneg (pk_pos k).le _).trans (pk_pow_le_Ik e k)

theorem abs_radialTransform_hk_le (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) :
    |radialTransform (e + 1) (hk k) v| ≤ 1 := by
  rcases le_or_gt 1 v with h1 | h1
  · rw [radialTransform_hk_of_one_le e k h1, abs_neg, abs_of_nonneg (Ik_nonneg e k)]
    exact Ik_le_one e k
  · unfold radialTransform
    have hv1 : v ^ (e + 1) ≤ 1 := pow_le_one₀ h0 h1.le
    have ha0 : 0 ≤ hk k v * v ^ (e + 1) := mul_nonneg (hk k).nonneg (pow_nonneg h0 _)
    have ha1 : hk k v * v ^ (e + 1) ≤ 1 := mul_le_one₀ (hk k).le_one (pow_nonneg h0 _) hv1
    have hb0 := integral_hk_nonneg e k h0
    have hb1 := (integral_hk_le e k h0).trans hv1
    rw [abs_le]
    constructor <;> linarith

theorem tendsto_Ik (e : ℕ) : Tendsto (Ik e) atTop (𝓝 1) := by
  have hp : Tendsto (fun k => pk k ^ (e + 1)) atTop (𝓝 1) := by
    simpa using tendsto_pk.pow (e + 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hp tendsto_const_nhds (pk_pow_le_Ik e) (Ik_le_one e)

theorem eventually_le_pk {v : ℝ} (hv : v < 1) : ∀ᶠ k in atTop, v ≤ pk k :=
  ((tendsto_order.1 tendsto_pk).1 v hv).mono fun _ h => h.le

end Radial

section Ball

variable {n : ℕ} (x : Fin n → ℂ)

theorem continuous_distSq : Continuous fun z : Fin n → ℂ => euclPot (z - x) :=
  (contDiff_euclPot n).continuous.comp (continuous_id.sub continuous_const)

theorem contDiff_distSq : ContDiff ℝ ∞ fun z : Fin n → ℂ => euclPot (z - x) :=
  (contDiff_euclPot n).comp (contDiff_id.sub contDiff_const)

theorem distSq_nonneg (z : Fin n → ℂ) : 0 ≤ euclPot (z - x) :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem mem_euclBall_iff_sq {ρ : ℝ} (hρ : 0 < ρ) (z : Fin n → ℂ) :
    z ∈ euclBall x ρ ↔ euclPot (z - x) < ρ ^ 2 :=
  Real.sqrt_lt' hρ

theorem measurableSet_euclBall (ρ : ℝ) : MeasurableSet (euclBall x ρ) :=
  (isOpen_lt (continuous_distSq x).sqrt continuous_const).measurableSet

theorem norm_sub_le_sqrt (z : Fin n → ℂ) : ‖z - x‖ ≤ Real.sqrt (euclPot (z - x)) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  have hj : ‖(z - x) j‖ ^ 2 ≤ euclPot (z - x) :=
    Finset.single_le_sum (f := fun j => ‖(z - x) j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have := Real.abs_le_sqrt hj
  rwa [abs_norm] at this

def bigBump (s : ℝ) : ContDiffBump (0 : ℝ) :=
  ⟨s ^ 2 + 1, 2 * (s ^ 2 + 1), by positivity, by nlinarith [sq_nonneg s]⟩

def majorant (s : ℝ) (z : Fin n → ℂ) : ℝ := bigBump s (euclPot (z - x))

theorem continuous_majorant (s : ℝ) : Continuous (majorant x s) :=
  (bigBump s).continuous.comp (continuous_distSq x)

theorem majorant_nonneg (s : ℝ) (z : Fin n → ℂ) : 0 ≤ majorant x s z := (bigBump s).nonneg

theorem majorant_one {s : ℝ} {z : Fin n → ℂ} (hz : euclPot (z - x) ≤ s ^ 2) : majorant x s z = 1 :=
  (bigBump s).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (distSq_nonneg x z)]
    show euclPot (z - x) ≤ s ^ 2 + 1
    linarith)

theorem hasCompactSupport_majorant (s : ℝ) : HasCompactSupport (majorant x s) := by
  refine HasCompactSupport.intro (isCompact_closedBall x (2 * (s ^ 2 + 1))) fun z hz => ?_
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hz
  have hR : 1 ≤ 2 * (s ^ 2 + 1) := by nlinarith [sq_nonneg s]
  have h1 : 2 * (s ^ 2 + 1) < Real.sqrt (euclPot (z - x)) := hz.trans_le (norm_sub_le_sqrt x z)
  have h2 : (2 * (s ^ 2 + 1)) ^ 2 < euclPot (z - x) := (Real.lt_sqrt (by linarith)).1 h1
  refine (bigBump s).zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (distSq_nonneg x z)]
  show 2 * (s ^ 2 + 1) ≤ euclPot (z - x)
  nlinarith

theorem abs_le_majorant {s C : ℝ} (hC : 0 ≤ C) {w : (Fin n → ℂ) → ℝ} (hw : ∀ z, |w z| ≤ C)
    (h0 : ∀ z, s ^ 2 ≤ euclPot (z - x) → w z = 0) (z : Fin n → ℂ) : |w z| ≤ C * majorant x s z := by
  rcases le_or_gt (s ^ 2) (euclPot (z - x)) with h | h
  · rw [h0 z h, abs_zero]
    exact mul_nonneg hC (majorant_nonneg x s z)
  · rw [majorant_one x h.le, mul_one]
    exact hw z

def smallBump {r : ℝ} (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  ⟨r ^ 2 / 8, r ^ 2 / 4, by positivity, by have := pow_pos hr 2; linarith⟩

def logDistSmooth {r : ℝ} (hr : 0 < r) (z : Fin n → ℂ) : ℝ :=
  Real.log (euclPot (z - x) + r ^ 2 * smallBump hr (euclPot (z - x)))

theorem distSq_add_pos {r : ℝ} (hr : 0 < r) (z : Fin n → ℂ) :
    0 < euclPot (z - x) + r ^ 2 * smallBump hr (euclPot (z - x)) := by
  have h0 := distSq_nonneg x z
  have hr2 := pow_pos hr 2
  rcases le_or_gt (euclPot (z - x)) (r ^ 2 / 8) with h | h
  · have h1 : smallBump hr (euclPot (z - x)) = 1 :=
      (smallBump hr).one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg h0]
        exact h)
    rw [h1]
    linarith
  · have := (smallBump hr).nonneg (x := euclPot (z - x))
    have : 0 ≤ r ^ 2 * smallBump hr (euclPot (z - x)) := mul_nonneg hr2.le this
    linarith [pow_pos hr 2]

theorem contDiff_logDistSmooth {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (logDistSmooth x hr) :=
  ((contDiff_distSq x).add (contDiff_const.mul ((smallBump hr).contDiff.comp (contDiff_distSq x)))).log
    fun z => (distSq_add_pos x hr z).ne'

theorem logDistSmooth_eventuallyEq {r : ℝ} (hr : 0 < r) {z : Fin n → ℂ} (hz : r ^ 2 / 4 < euclPot (z - x)) :
    logDistSmooth x hr =ᶠ[𝓝 z] logDistSq x := by
  refine Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const (continuous_distSq x)).mem_nhds hz)
    fun z' hz' => ?_
  have h0 : smallBump hr (euclPot (z' - x)) = 0 :=
    (smallBump hr).zero_of_le_dist (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (distSq_nonneg x z')]
      exact (le_of_lt hz'))
  simp only [logDistSmooth, logDistSq]
  rw [h0, mul_zero, add_zero]

theorem tendsto_hk_indicator {ρ : ℝ} (hρ : 0 < ρ) (z : Fin n → ℂ) :
    Tendsto (fun k => hk k (euclPot (z - x) / ρ ^ 2)) atTop
      (𝓝 ((euclBall x ρ).indicator (fun _ => (1 : ℝ)) z)) := by
  have hρ2 := pow_pos hρ 2
  have hv0 : 0 ≤ euclPot (z - x) / ρ ^ 2 := div_nonneg (distSq_nonneg x z) hρ2.le
  by_cases hz : euclPot (z - x) < ρ ^ 2
  · rw [Set.indicator_of_mem ((mem_euclBall_iff_sq x hρ z).2 hz)]
    have hv : euclPot (z - x) / ρ ^ 2 < 1 := (div_lt_one hρ2).2 hz
    exact tendsto_const_nhds.congr' ((eventually_le_pk hv).mono fun k hk' => (hk_one hv0 hk').symm)
  · rw [Set.indicator_of_notMem (fun h => hz ((mem_euclBall_iff_sq x hρ z).1 h))]
    have hv : 1 ≤ euclPot (z - x) / ρ ^ 2 := (one_le_div hρ2).2 (not_lt.1 hz)
    simp only [hk_zero_of_one_le hv]
    exact tendsto_const_nhds

end Ball

section Weights

variable {r s : ℝ} (e : ℕ)

def annWeight (r s : ℝ) (e k : ℕ) (t : ℝ) : ℝ :=
  r ^ (2 * (e + 1)) * hk k (t / s ^ 2) - s ^ (2 * (e + 1)) * hk k (t / r ^ 2)

theorem contDiff_annWeight (k : ℕ) : ContDiff ℝ ∞ (annWeight r s e k) :=
  (contDiff_const.mul ((hk k).contDiff.comp (contDiff_id.div_const _))).sub
    (contDiff_const.mul ((hk k).contDiff.comp (contDiff_id.div_const _)))

theorem annWeight_zero_of_le (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (ht : s ^ 2 ≤ t) :
    annWeight r s e k t = 0 := by
  have hr2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  unfold annWeight
  rw [hk_zero_of_one_le ((one_le_div (hr2.trans_le hs2)).2 ht),
    hk_zero_of_one_le ((one_le_div hr2).2 (hs2.trans ht))]
  ring

theorem annWeight_const (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 (pk k * r ^ 2)) :
    annWeight r s e k t = annWeight r s e k 0 := by
  have hr2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  have h1 : t / r ^ 2 ≤ pk k := (div_le_iff₀ hr2).2 ht.2
  have h2 : t / s ^ 2 ≤ t / r ^ 2 := div_le_div_of_nonneg_left ht.1 hr2 hs2
  unfold annWeight
  rw [hk_one (div_nonneg ht.1 (hr2.trans_le hs2).le) (h2.trans h1), hk_one (div_nonneg ht.1 hr2.le) h1,
    zero_div, zero_div, hk_one le_rfl (pk_pos k).le]

theorem abs_annWeight_le (hr : 0 < r) (hs : 0 < s) (k : ℕ) (t : ℝ) :
    |annWeight r s e k t| ≤ r ^ (2 * (e + 1)) + s ^ (2 * (e + 1)) := by
  have hb : ∀ (c v : ℝ), 0 ≤ c → |c * hk k v| ≤ c := fun c v hc => by
    rw [abs_mul, abs_of_nonneg hc, abs_of_nonneg (hk k).nonneg]
    exact mul_le_of_le_one_right hc (hk k).le_one
  exact (abs_sub _ _).trans (add_le_add (hb _ _ (pow_nonneg hr.le _)) (hb _ _ (pow_nonneg hs.le _)))

theorem radialTransform_annWeight (hr : 0 < r) (hs : 0 < s) (k : ℕ) (t : ℝ) :
    radialTransform (e + 1) (annWeight r s e k) t =
      r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
        (radialTransform (e + 1) (hk k) (t / s ^ 2) - radialTransform (e + 1) (hk k) (t / r ^ 2)) := by
  rw [show annWeight r s e k =
      (fun τ => r ^ (2 * (e + 1)) * hk k (τ / s ^ 2) - s ^ (2 * (e + 1)) * hk k (τ / r ^ 2)) from rfl,
    radialTransform_sub e (f₁ := fun τ => hk k (τ / s ^ 2)) (f₂ := fun τ => hk k (τ / r ^ 2))
      ((hk k).continuous.comp (continuous_id.div_const _)) ((hk k).continuous.comp (continuous_id.div_const _)),
    radialTransform_comp_div e (hk k) hs.ne', radialTransform_comp_div e (hk k) hr.ne']
  ring

theorem radialTransform_diff_of_le (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (h0 : 0 ≤ t)
    (ht : t ≤ pk k * r ^ 2) :
    radialTransform (e + 1) (hk k) (t / s ^ 2) - radialTransform (e + 1) (hk k) (t / r ^ 2) = 0 := by
  have hr2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  have h1 : t / r ^ 2 ≤ pk k := (div_le_iff₀ hr2).2 ht
  have h2 : t / s ^ 2 ≤ t / r ^ 2 := div_le_div_of_nonneg_left h0 hr2 hs2
  rw [radialTransform_hk_of_le e k (div_nonneg h0 (hr2.trans_le hs2).le) (h2.trans h1),
    radialTransform_hk_of_le e k (div_nonneg h0 hr2.le) h1, sub_self]

theorem radialTransform_diff_of_ge (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (ht : s ^ 2 ≤ t) :
    radialTransform (e + 1) (hk k) (t / s ^ 2) - radialTransform (e + 1) (hk k) (t / r ^ 2) = 0 := by
  have hr2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  rw [radialTransform_hk_of_one_le e k ((one_le_div (hr2.trans_le hs2)).2 ht),
    radialTransform_hk_of_one_le e k ((one_le_div hr2).2 (hs2.trans ht)), sub_self]

variable {n : ℕ} (x : Fin n → ℂ)

theorem tendsto_radialTransform_diff (hr : 0 < r) (hrs : r ≤ s) (z : Fin n → ℂ) :
    Tendsto (fun k => radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
        radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)) atTop
      (𝓝 ((euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)) := by
  have hs : 0 < s := hr.trans_le hrs
  have hr2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  have h0 := distSq_nonneg x z
  rcases lt_or_ge (euclPot (z - x)) (r ^ 2) with h1 | h1
  · rw [Set.indicator_of_notMem (fun h => h.2 ((mem_euclBall_iff_sq x hr z).2 h1))]
    refine tendsto_const_nhds.congr' ((eventually_le_pk ((div_lt_one hr2).2 h1)).mono fun k hk' => ?_)
    exact (radialTransform_diff_of_le e hr hrs k h0 ((div_le_iff₀ hr2).1 hk')).symm
  rcases lt_or_ge (euclPot (z - x)) (s ^ 2) with h2 | h2
  · rw [Set.indicator_of_mem (show z ∈ euclBall x s \ euclBall x r from ⟨(mem_euclBall_iff_sq x hs z).2 h2,
      fun h => (not_lt.2 h1) ((mem_euclBall_iff_sq x hr z).1 h)⟩)]
    have hv : euclPot (z - x) / s ^ 2 < 1 := (div_lt_one (hr2.trans_le hs2)).2 h2
    refine (tendsto_Ik e).congr' ((eventually_le_pk hv).mono fun k hk' => ?_)
    beta_reduce
    rw [radialTransform_hk_of_le e k (div_nonneg h0 (hr2.trans_le hs2).le) hk',
      radialTransform_hk_of_one_le e k ((one_le_div hr2).2 h1)]
    ring
  · rw [Set.indicator_of_notMem (fun h => (not_lt.2 h2) ((mem_euclBall_iff_sq x hs z).1 h.1))]
    simp only [radialTransform_diff_of_ge e hr hrs _ h2]
    exact tendsto_const_nhds

end Weights

end RegLelongAnnulus

open RegLelongAnnulus in

theorem RegLelongAnnulus.proof (hRW : RegRadialWeight.Statement) (hCM : ChartMassCompact.Statement) :
    RegLelongAnnulus.Statement := by
  intro n d J A u ε x r s hJ hdim hAf hε hr hrs
  have hs : 0 < s := hr.trans_le hrs
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  have hφσ : ∀ k, SmoothNear (zeroSet J)
      ((vecCons (logReg u ε) fun _ => euclPot : Fin (d + 1) → (Fin n → ℂ) → ℝ) k) := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_euclPot n)
  have hball : ∀ ρ, 0 < ρ → ρ ≤ s → Integrable (chartDens J A ((euclBall x ρ).indicator fun _ => (1 : ℝ))
      (vecCons (logReg u ε) fun _ => euclPot)) := by
    intro ρ hρ hρs
    refine integrable_chartDens hCM hJ hdim hAf hφσ (continuous_majorant x s) (hasCompactSupport_majorant x s)
      zero_le_one (measurable_const.indicator (measurableSet_euclBall x ρ))
      (abs_le_majorant x zero_le_one (fun z => ?_) (fun z hz => ?_))
    · by_cases h : z ∈ euclBall x ρ <;> simp [h]
    · refine Set.indicator_of_notMem (fun h => ?_) _
      have h1 := (mem_euclBall_iff_sq x hρ z).1 h
      have h2 : ρ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hρ.le hρs 2
      linarith
  rcases d with _ | e
  ·
    have hφ : (fun _ : Fin 0 => logDistSq x) = fun _ => euclPot := Subsingleton.elim _ _
    rw [hφ]
    have hsub : ((euclBall x s \ euclBall x r).indicator fun _ => (1 : ℝ)) = fun z =>
        1 * (euclBall x s).indicator (fun _ => (1 : ℝ)) z - 1 * (euclBall x r).indicator (fun _ => (1 : ℝ)) z := by
      funext z
      by_cases h1 : z ∈ euclBall x r
      · have h2 : z ∈ euclBall x s :=
          (mem_euclBall_iff_sq x hs z).2 (((mem_euclBall_iff_sq x hr z).1 h1).trans_le hs2)
        simp [h1, h2]
      · by_cases h2 : z ∈ euclBall x s <;> simp [h1, h2]
    rw [hsub]
    simp only [chartDens_sub' hAf]
    rw [integral_sub ((hball s hs le_rfl).const_mul 1) ((hball r hr hrs).const_mul 1), integral_const_mul,
      integral_const_mul]
    simp
  · have hc0 : 0 ≤ r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) := mul_nonneg (pow_nonneg hr.le _) (pow_nonneg hs.le _)

    have hEq : ∀ k, ∫ y, chartDens J A (fun z => annWeight r s e k (euclPot (z - x)))
          (vecCons (logReg u ε) fun _ => euclPot) y =
        ∫ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
            (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
              radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y := by
      intro k
      have hT : (∫ τ in (0 : ℝ)..s ^ 2, annWeight r s e k τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) = 0 := by
        have h := radialTransform_annWeight e hr hs k (s ^ 2)
        rw [div_self (pow_pos hs 2).ne', radialTransform_hk_of_one_le e k le_rfl,
          radialTransform_hk_of_one_le e k ((one_le_div hr2).2 hs2), sub_self, mul_zero] at h
        unfold radialTransform at h
        rw [annWeight_zero_of_le e hr hrs k le_rfl, zero_mul, zero_sub, neg_eq_zero] at h
        exact h
      have h := hRW n (e + 1) J A u ε x (annWeight r s e k) (pk k * r ^ 2) (s ^ 2) hJ hdim hAf hε
        (contDiff_annWeight e k) (mul_pos (pk_pos k) hr2) (fun t ht => annWeight_const e hr hrs k ht)
        (fun t ht => annWeight_zero_of_le e hr hrs k ht) hT
      have hw : (fun z => radialTransform (e + 1) (annWeight r s e k) (euclPot (z - x))) = fun z =>
          r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) * (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)) :=
        funext fun z => radialTransform_annWeight e hr hs k _
      rw [h, hw]

    have hL : Tendsto (fun k => ∫ y, chartDens J A (fun z => annWeight r s e k (euclPot (z - x)))
          (vecCons (logReg u ε) fun _ => euclPot) y) atTop
        (𝓝 (r ^ (2 * (e + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y) -
          s ^ (2 * (e + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y)) := by
      have h := tendsto_integral_chartDens hCM hJ hdim hAf hφσ (continuous_majorant x s)
        (hasCompactSupport_majorant x s) (C := r ^ (2 * (e + 1)) + s ^ (2 * (e + 1)))
        (add_nonneg (pow_nonneg hr.le _) (pow_nonneg hs.le _))
        (w := fun k z => annWeight r s e k (euclPot (z - x)))
        (w' := fun z => r ^ (2 * (e + 1)) * (euclBall x s).indicator (fun _ => (1 : ℝ)) z -
          s ^ (2 * (e + 1)) * (euclBall x r).indicator (fun _ => (1 : ℝ)) z)
        (fun k => ((contDiff_annWeight e k).continuous.comp (continuous_distSq x)).measurable)
        (fun k => abs_le_majorant x (add_nonneg (pow_nonneg hr.le _) (pow_nonneg hs.le _))
          (fun z => abs_annWeight_le e hr hs k _) (fun z hz => annWeight_zero_of_le e hr hrs k hz))
        (fun z => ((tendsto_hk_indicator x hs z).const_mul _).sub ((tendsto_hk_indicator x hr z).const_mul _))
      have hlim : ∫ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * (euclBall x s).indicator (fun _ => (1 : ℝ)) z -
            s ^ (2 * (e + 1)) * (euclBall x r).indicator (fun _ => (1 : ℝ)) z)
            (vecCons (logReg u ε) fun _ => euclPot) y =
          r ^ (2 * (e + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y) -
          s ^ (2 * (e + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y := by
        simp only [chartDens_sub' hAf]
        rw [integral_sub ((hball s hs le_rfl).const_mul _) ((hball r hr hrs).const_mul _), integral_const_mul,
          integral_const_mul]
      rw [← hlim]
      exact h

    have hφτ : ∀ k, SmoothNear (zeroSet J)
        ((vecCons (logReg u ε) fun _ => logDistSmooth x hr : Fin (e + 1 + 1) → (Fin n → ℂ) → ℝ) k) := by
      intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
      · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logDistSmooth x hr)
    have hgerm : ∀ z : Fin n → ℂ, r ^ 2 / 4 < euclPot (z - x) → ∀ i : Fin (e + 1 + 1),
        (vecCons (logReg u ε) fun _ => logDistSq x : Fin (e + 1 + 1) → (Fin n → ℂ) → ℝ) i =ᶠ[𝓝 z]
          (vecCons (logReg u ε) fun _ => logDistSmooth x hr : Fin (e + 1 + 1) → (Fin n → ℂ) → ℝ) i := by
      intro z hz i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Matrix.cons_val_zero]
        exact Filter.EventuallyEq.rfl
      · simp only [Matrix.cons_val_succ]
        exact (logDistSmooth_eventuallyEq x hr hz).symm
    have hloc : ∀ k y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y =
        chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
          (vecCons (logReg u ε) fun _ => logDistSmooth x hr) y := by
      intro k y
      refine chartDens_congr_fun (fun z _ hz => hgerm z ?_) y
      by_contra hle
      replace hle := not_lt.1 hle
      apply hz
      have hp := half_le_pk k
      rw [radialTransform_diff_of_le e hr hrs k (distSq_nonneg x z) (by nlinarith), mul_zero]
    have hloc' : ∀ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
          (vecCons (logReg u ε) fun _ => logDistSq x) y =
        chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
          (vecCons (logReg u ε) fun _ => logDistSmooth x hr) y := by
      intro y
      refine chartDens_congr_fun (fun z _ hz => hgerm z ?_) y
      by_contra hle
      replace hle := not_lt.1 hle
      apply hz
      rw [Set.indicator_of_notMem (fun h => h.2 ((mem_euclBall_iff_sq x hr z).2 (by linarith))), mul_zero]
    have hR : Tendsto (fun k => ∫ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y) atTop
        (𝓝 (r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => logDistSq x) y)) := by
      have h := tendsto_integral_chartDens hCM hJ hdim hAf hφτ (continuous_majorant x s)
        (hasCompactSupport_majorant x s) (C := 2 * (r ^ (2 * (e + 1)) * s ^ (2 * (e + 1))))
        (by positivity)
        (w := fun k z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
        (w' := fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
        (fun k => (continuous_const.mul
          (((continuous_radialTransform e (hk k).continuous).comp ((continuous_distSq x).div_const _)).sub
            ((continuous_radialTransform e (hk k).continuous).comp
              ((continuous_distSq x).div_const _)))).measurable)
        (fun k => abs_le_majorant x (by positivity) (fun z => ?_)
          (fun z hz => by rw [radialTransform_diff_of_ge e hr hrs k hz, mul_zero]))
        (fun z => (tendsto_radialTransform_diff e x hr hrs z).const_mul _)
      · have hl : ∀ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
              (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
              (vecCons (logReg u ε) fun _ => logDistSq x) y =
            r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) * chartDens J A
              ((euclBall x s \ euclBall x r).indicator fun _ => 1) (vecCons (logReg u ε) fun _ => logDistSq x) y :=
          fun y => chartDens_const_mul hAf _ _ _ y
        rw [← integral_const_mul]
        simp only [← hl, hloc', hloc]
        exact h
      · have h1 := abs_radialTransform_hk_le e k (div_nonneg (distSq_nonneg x z) (pow_pos hs 2).le)
        have h2 := abs_radialTransform_hk_le e k (div_nonneg (distSq_nonneg x z) hr2.le)
        rw [abs_mul, abs_of_nonneg hc0]
        have h3 := abs_sub (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2))
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2))
        nlinarith
    exact tendsto_nhds_unique hL (hR.congr fun k => (hEq k).symm)

end

end GroundTheory.Heights₂.Heights
