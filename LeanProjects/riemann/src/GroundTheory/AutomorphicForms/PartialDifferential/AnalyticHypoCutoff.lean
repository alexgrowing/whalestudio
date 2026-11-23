import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoBasic

namespace GroundTheory.Automorphic.Sobolev

open MeasureTheory
open scoped ContDiff Nat

noncomputable section

section Finite

variable {ι : Type*} [Fintype ι]

theorem sqrt_sum_sq_eq_norm (x : ι → ℝ) :
    Real.sqrt (∑ i, x i ^ 2) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [Real.norm_eq_abs, sq_abs]

theorem sqrt_sum_sq_add_le (x y : ι → ℝ) :
    Real.sqrt (∑ i, (x i + y i) ^ 2) ≤ Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2) := by
  rw [sqrt_sum_sq_eq_norm, sqrt_sum_sq_eq_norm, sqrt_sum_sq_eq_norm]
  have : (WithLp.toLp 2 (fun i ↦ x i + y i) : EuclideanSpace ℝ ι) =
      WithLp.toLp 2 x + WithLp.toLp 2 y := by
    ext i; simp
  rw [this]
  exact norm_add_le _ _

theorem sqrt_sum_sq_sum_le {τ : Type*} (T : Finset τ) (y : τ → ι → ℝ) :
    Real.sqrt (∑ i, (∑ t ∈ T, y t i) ^ 2) ≤ ∑ t ∈ T, Real.sqrt (∑ i, y t i ^ 2) := by
  simp_rw [sqrt_sum_sq_eq_norm]
  have : (WithLp.toLp 2 (fun i ↦ ∑ t ∈ T, y t i) : EuclideanSpace ℝ ι) =
      ∑ t ∈ T, WithLp.toLp 2 (y t) := by
    ext i; simp
  rw [this]
  exact norm_sum_le _ _

theorem sqrt_sum_sq_mono_abs {x y : ι → ℝ} (h : ∀ i, |x i| ≤ y i) :
    Real.sqrt (∑ i, x i ^ 2) ≤ Real.sqrt (∑ i, y i ^ 2) := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [← sq_abs (x i)]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem sqrt_sum_sq_mono {x y : ι → ℝ} (h : ∀ i, 0 ≤ x i ∧ x i ≤ y i) :
    Real.sqrt (∑ i, x i ^ 2) ≤ Real.sqrt (∑ i, y i ^ 2) :=
  sqrt_sum_sq_mono_abs fun i ↦ by rw [abs_of_nonneg (h i).1]; exact (h i).2

theorem sqrt_sum_sq_const_mul (c : ℝ) (x : ι → ℝ) :
    Real.sqrt (∑ i, (c * x i) ^ 2) = |c| * Real.sqrt (∑ i, x i ^ 2) := by
  have : ∑ i, (c * x i) ^ 2 = c ^ 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem sqrt_sum_sq_le_sum {ι τ : Type*} [Fintype ι] (T : Finset τ) (x : ι → ℝ) (c : τ → ℝ)
    (y : τ → ι → ℝ) (hc : ∀ t ∈ T, 0 ≤ c t) (hx : ∀ i, |x i| ≤ ∑ t ∈ T, c t * y t i) :
    Real.sqrt (∑ i, x i ^ 2) ≤ ∑ t ∈ T, c t * Real.sqrt (∑ i, y t i ^ 2) := by
  calc Real.sqrt (∑ i, x i ^ 2) ≤ Real.sqrt (∑ i, (∑ t ∈ T, c t * y t i) ^ 2) :=
        sqrt_sum_sq_mono_abs hx
    _ ≤ ∑ t ∈ T, Real.sqrt (∑ i, (c t * y t i) ^ 2) := sqrt_sum_sq_sum_le T _
    _ = ∑ t ∈ T, c t * Real.sqrt (∑ i, y t i ^ 2) := by
        refine Finset.sum_congr rfl fun t ht ↦ ?_
        rw [sqrt_sum_sq_const_mul, abs_of_nonneg (hc t ht)]

end Finite

section L2

variable {n : ℕ}

theorem memLp_two_of_continuous_hasCompactSupport {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) : MemLp f 2 volume :=
  hf.memLp_of_hasCompactSupport hc

theorem l2Norm_le_of_abs_le {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 volume)
    (_hf : AEStronglyMeasurable f volume) (h : ∀ x, |f x| ≤ g x) : l2n f ≤ l2n g := by
  refine ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_real fun x ↦ ?_)
  rw [Real.norm_eq_abs]; exact h x

theorem l2Norm_add_le_alt {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : l2n (fun x ↦ f x + g x) ≤ l2n f + l2n g := by
  have h := eLpNorm_add_le hf.1 hg.1 (p := 2) (μ := volume) one_le_two
  rw [l2n, l2n, l2n, ← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩) h

theorem l2Norm_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ∀ i ∈ s, MemLp (F i) 2 volume) : l2n (fun x ↦ ∑ i ∈ s, F i x) ≤ ∑ i ∈ s, l2n (F i) := by
  have h := eLpNorm_sum_le (μ := volume) (p := 2) (s := s) (f := F) (fun i hi ↦ (hF i hi).1)
    one_le_two
  have e : (fun x ↦ ∑ i ∈ s, F i x) = ∑ i ∈ s, F i := by
    funext x; simp [Finset.sum_apply]
  simp only [l2n]
  rw [e, ← ENNReal.toReal_sum fun i hi ↦ (hF i hi).eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i hi ↦ (hF i hi).eLpNorm_ne_top) h

theorem l2Norm_const_mul (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    l2n (fun x ↦ c * f x) = |c| * l2n f := by
  have h := eLpNorm_const_smul (μ := volume) (p := 2) c f
  have e : (fun x ↦ c * f x) = c • f := by funext x; simp
  rw [l2n, e, h, l2n, ENNReal.toReal_mul]
  simp [Real.norm_eq_abs]

theorem l2Norm_eq_sqrt_integral_sq {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 volume) :
    l2n f = Real.sqrt (∫ x, f x ^ 2) := by
  rw [l2n, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  have e : ∫ x, ‖f x‖ ^ (ENNReal.toReal 2) = ∫ x, f x ^ 2 := by
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp [Real.norm_eq_abs, sq_abs]
  rw [e]
  norm_num

theorem l2Norm_sqrt_sum_sq_eq {ι : Type*} [Fintype ι] (F : ι → EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ∀ i, MemLp (F i) 2 volume) :
    l2n (fun x ↦ Real.sqrt (∑ i, F i x ^ 2)) = Real.sqrt (∑ i, l2n (F i) ^ 2) := by
  have hint : Integrable (fun x ↦ ∑ i, F i x ^ 2) volume :=
    integrable_finsetSum _ fun i _ ↦ (hF i).integrable_sq
  have hmeas : AEStronglyMeasurable (fun x ↦ Real.sqrt (∑ i, F i x ^ 2)) volume := by
    have : AEStronglyMeasurable (fun x ↦ ∑ i, F i x ^ 2) volume := hint.1
    exact Real.continuous_sqrt.comp_aestronglyMeasurable this
  have hsq : ∀ x, Real.sqrt (∑ i, F i x ^ 2) ^ 2 = ∑ i, F i x ^ 2 := fun x ↦
    Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  have hmem : MemLp (fun x ↦ Real.sqrt (∑ i, F i x ^ 2)) 2 volume := by
    rw [memLp_two_iff_integrable_sq hmeas]
    simp_rw [hsq]
    exact hint
  rw [l2Norm_eq_sqrt_integral_sq hmem]
  simp_rw [hsq]
  rw [integral_finsetSum _ fun i _ ↦ (hF i).integrable_sq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [l2Norm_eq_sqrt_integral_sq (hF i), Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg _)]

end L2

section Cutoff

variable {n : ℕ}

theorem exists_cutoff (x₀ : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    ∃ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ tsupport χ ⊆ Metric.ball x₀ R ∧
      ∀ x ∈ Metric.ball x₀ (R / 2), χ x = 1 := by
  let bmp : ContDiffBump x₀ := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  refine ⟨bmp, bmp.contDiff, bmp.hasCompactSupport, fun x ↦ ⟨bmp.nonneg, bmp.le_one⟩, ?_, fun x hx ↦ ?_⟩
  · rw [bmp.tsupport_eq]
    exact Metric.closedBall_subset_ball (show 3 * R / 4 < R by linarith)
  · exact bmp.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)

theorem exists_norm_iteratedFDeriv_pow_le {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (L : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L → i ≤ s →
      ‖iteratedFDeriv ℝ i (fun y ↦ ((χ y : ℂ)) ^ s) x‖ ≤ K * (s : ℝ) ^ i * χ x ^ (s - i) := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ C := fun j ↦
    (hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hχc.iteratedFDeriv j)
  choose C hC using hb
  set D : ℝ := 1 + ∑ j ∈ Finset.range (L + 1), |C j| with hD
  have hD1 : 1 ≤ D := by
    rw [hD]; linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.range (L + 1)) ↦ abs_nonneg (C j)]
  have hDj : ∀ j ≤ L, ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ D := by
    intro j hj x
    calc ‖iteratedFDeriv ℝ j χ x‖ ≤ C j := hC j x
      _ ≤ |C j| := le_abs_self _
      _ ≤ ∑ j ∈ Finset.range (L + 1), |C j| :=
          Finset.single_le_sum (f := fun j ↦ |C j|) (fun j _ ↦ abs_nonneg _)
            (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
      _ ≤ D := by rw [hD]; linarith
  refine ⟨(L ! : ℝ) * D ^ L, by positivity, fun s i x hiL his ↦ ?_⟩
  have hfun : (fun y ↦ ((χ y : ℂ)) ^ s) =
      Complex.ofRealLI ∘ ((fun t : ℝ ↦ t ^ s) ∘ χ) := by
    funext y; simp
  have hcomp : ContDiff ℝ ∞ ((fun t : ℝ ↦ t ^ s) ∘ χ) := (contDiff_id.pow s).comp hχ
  rw [hfun, LinearIsometry.norm_iteratedFDeriv_comp_left _ hcomp.contDiffAt
    (by exact_mod_cast le_top)]
  obtain ⟨h0, h1⟩ := h01 x
  have key := norm_iteratedFDeriv_comp_le (g := fun t : ℝ ↦ t ^ s) (f := χ) (n := i)
    (contDiff_id.pow s) hχ (by exact_mod_cast le_top) x
    (C := (s : ℝ) ^ i * χ x ^ (s - i)) (D := D) (fun j hj ↦ ?_) (fun j hj1 hj ↦ ?_)
  · calc ‖iteratedFDeriv ℝ i ((fun t : ℝ ↦ t ^ s) ∘ χ) x‖
        ≤ i ! * ((s : ℝ) ^ i * χ x ^ (s - i)) * D ^ i := key
      _ ≤ L ! * ((s : ℝ) ^ i * χ x ^ (s - i)) * D ^ L := by
          have h1' : (i ! : ℝ) ≤ L ! := by exact_mod_cast Nat.factorial_le hiL
          have h2' : D ^ i ≤ D ^ L := pow_le_pow_right₀ hD1 hiL
          gcongr
      _ = (L ! : ℝ) * D ^ L * (s : ℝ) ^ i * χ x ^ (s - i) := by ring
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_pow, norm_mul, norm_pow,
      Real.norm_of_nonneg h0, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hjs : j ≤ s := hj.trans his
    have hsj : (s : ℝ) ^ j ≤ (s : ℝ) ^ i := by
      rcases Nat.eq_zero_or_pos s with hs | hs
      · have hi0 : i = 0 := by omega
        have hj0 : j = 0 := by omega
        rw [hi0, hj0]
      · exact pow_le_pow_right₀ (Nat.one_le_cast.mpr hs) hj
    calc (s.descFactorial j : ℝ) * χ x ^ (s - j) ≤ (s : ℝ) ^ j * χ x ^ (s - i) :=
          mul_le_mul (by exact_mod_cast Nat.descFactorial_le_pow s j)
            (pow_le_pow_of_le_one h0 h1 (by omega)) (by positivity) (by positivity)
      _ ≤ (s : ℝ) ^ i * χ x ^ (s - i) := mul_le_mul_of_nonneg_right hsj (by positivity)
  · exact (hDj j (hj.trans hiL) x).trans (le_self_pow₀ hD1 (by omega))

end Cutoff

end

end GroundTheory.Automorphic.Sobolev
