import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMA

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem hasDerivAt_phiE (c : ℝ) (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (R : PX m n)
    (y : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun σ => evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y))
      (evX (DMp ε c H R) (mulR (aE H s) y) * gs c (mulR (aE H s) y)) s := by
  have hR : HasDerivAt (fun σ => evX R (mulR (aE H σ) y)) (evX (eulH H R) (mulR (aE H s) y)) s := by
    rw [evX_eulH]
    exact hasDerivAt_eval_curve R (fun σ => ept (mulR (aE H σ) y)) _ s
      (fun k => hasDerivAt_ept H y s k)
  refine (hR.mul (hasDerivAt_gsE c ε hH y s)).congr_deriv ?_
  simp only [DMp, trHQ, evX_eq, map_sub, map_mul, MvPolynomial.eval_C]
  ring

theorem norm_mulR_le (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    ‖mulR A y‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  calc ‖mulR A y a j‖ = ‖∑ i, y a i * A i j‖ := rfl
    _ ≤ ∑ i, ‖y a i * A i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖y‖ * ‖A i j‖ := by
        gcongr with i
        rw [norm_mul]
        gcongr
        exact (norm_le_pi_norm (y a) i).trans (norm_le_pi_norm y a)
    _ = ‖y‖ * ∑ i, ‖A i j‖ := by rw [Finset.mul_sum]
    _ ≤ ‖y‖ * ∑ i, ∑ j, ‖A i j‖ := by
        gcongr with i
        exact Finset.single_le_sum (f := fun j => ‖A i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ = _ := mul_comm _ _

theorem continuous_aE_entry (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : Continuous fun σ : ℝ => aE H σ i j :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_aE_entry H s i j).continuousAt

theorem dom_boundE (c : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℂ) (P : PX m n) (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, |σ - s| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  have hr0 : 0 ≤ r := by positivity
  obtain ⟨Cp, k, hCp, hP⟩ := PositivityTheory.Rg.Sw.AbsSt.DF.poly_bound P
  obtain ⟨Cd, hCd, hdec⟩ := PositivityTheory.Rg.Sw.AbsSt.DF.decay k c hc r
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := s - 1) (b := s + 1)).exists_bound_of_continuousOn
    (f := fun σ : ℝ => ∑ i, ∑ j, ‖aE H (-σ) i j‖)
    (Continuous.continuousOn (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      ((continuous_aE_entry H i j).comp continuous_neg).norm))
  set L' := max L 1 with hL'
  have hL'1 : 1 ≤ L' := le_max_right _ _
  have hL'0 : 0 ≤ L' := by linarith
  refine ⟨Cp * Cd * L' ^ r, mul_nonneg (mul_nonneg hCp hCd) (Real.rpow_nonneg hL'0 r),
    fun σ hσ y => ?_⟩
  set z := mulR (aE H σ) y with hz
  have hσI : σ ∈ Icc (s - 1) (s + 1) := by
    rw [abs_lt] at hσ
    constructor <;> linarith [hσ.1, hσ.2]
  have hsum : ∑ i, ∑ j, ‖aE H (-σ) i j‖ ≤ L' := by
    have := hL σ hσI
    rw [Real.norm_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  have hy : ‖y‖ ≤ L' * ‖z‖ := by
    have hyz : y = mulR (aE H (-σ)) z := by rw [hz, mulR_mul, aE_mul_neg', mulR_one]
    calc ‖y‖ = ‖mulR (aE H (-σ)) z‖ := by rw [← hyz]
      _ ≤ (∑ i, ∑ j, ‖aE H (-σ) i j‖) * ‖z‖ := norm_mulR_le _ _
      _ ≤ L' * ‖z‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have hg : ‖gs c z‖ ≤ Real.exp (-(c * ‖z‖ ^ 2)) := by
    rw [gs, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (PositivityTheory.Rg.Sw.AbsSt.DF.sq_norm_le_sum z) hc.le))
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hmain : ‖evX P z * gs c z‖ ≤ Cp * Cd * (1 + ‖z‖) ^ (-r) := by
    rw [norm_mul]
    calc ‖evX P z‖ * ‖gs c z‖ ≤ (Cp * (1 + ‖z‖) ^ k) * Real.exp (-(c * ‖z‖ ^ 2)) :=
          mul_le_mul (hP z) hg (norm_nonneg _) (by positivity)
      _ = Cp * ((1 + ‖z‖) ^ k * Real.exp (-(c * ‖z‖ ^ 2))) := by ring
      _ ≤ Cp * (Cd * (1 + ‖z‖) ^ (-r)) := mul_le_mul_of_nonneg_left (hdec _ hz0) hCp
      _ = _ := by ring
  have hcmp : (1 + ‖z‖) ^ (-r) ≤ L' ^ r * (1 + ‖y‖) ^ (-r) := by
    have h1 : 1 + ‖y‖ ≤ L' * (1 + ‖z‖) := by nlinarith
    have h2 : (L' * (1 + ‖z‖)) ^ (-r) ≤ (1 + ‖y‖) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    rw [Real.mul_rpow hL'0 (by positivity)] at h2
    calc (1 + ‖z‖) ^ (-r) = L' ^ r * (L' ^ (-r) * (1 + ‖z‖) ^ (-r)) := by
          rw [← mul_assoc, ← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ L' ^ r * (1 + ‖y‖) ^ (-r) := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hL'0 r)
  calc ‖evX P z * gs c z‖ ≤ Cp * Cd * (1 + ‖z‖) ^ (-r) := hmain
    _ ≤ Cp * Cd * (L' ^ r * (1 + ‖y‖) ^ (-r)) :=
        mul_le_mul_of_nonneg_left hcmp (mul_nonneg hCp hCd)
    _ = _ := by ring

end PositivityTheory.Rg.Sw.AbsSt.SDM
