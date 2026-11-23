import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDivisionNearSChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace DivisionNearS

variable {D : ℕ}

theorem exp_identity (T : ℕ) (t G g₂ E φc : ℝ) (hG : 0 < G) (hg₂ : 0 < g₂) :
    g₂ * G ^ (D + T) * G ^ (-(t + 1)) *
        Real.exp (-(φc + Real.log g₂ + (D : ℝ) * Real.log G +
          ((T : ℝ) - 1 - t) * (Real.log G + Real.log E))) =
      Real.exp (-(φc + ((T : ℝ) - 1 - t) * Real.log E)) := by
  obtain ⟨a, rfl⟩ : ∃ a, g₂ = Real.exp a := ⟨_, (Real.exp_log hg₂).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, G = Real.exp b := ⟨_, (Real.exp_log hG).symm⟩
  rw [Real.log_exp, Real.log_exp, ← Real.rpow_natCast, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem dens_transform (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D)
    (T : ℕ) (t : ℝ) (F : Fin X.A.n → X.U → ℂ) (hF : F ∈ topSections X.A X.L₂ X.L (D + T))
    (j c : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    2 ^ D * ‖F j x‖ ^ 2 * (∑ i, ‖Z.s i j x‖ ^ 2) ^ (-(t + 1)) *
        Real.exp (-(φA.φ j x + ((T : ℝ) - 1 - t) * fsWeight X.e j x)) =
      ‖jac X.A j c x‖ ^ 2 * (2 ^ D * ‖F c x‖ ^ 2 * (∑ i, ‖Z.s i c x‖ ^ 2) ^ (-(t + 1)) *
        Real.exp (-(φA.φ c x + ((T : ℝ) - 1 - t) * fsWeight X.e c x))) := by
  have hG : 0 < ‖X.L.g j c x‖ ^ 2 := by
    have := X.L.ne_zero j c x hx; positivity
  have hg₂ : 0 < ‖X.L₂.g j c x‖ ^ 2 := by
    have := X.L₂.ne_zero j c x hx; positivity
  have hE := esum_pos X c x hx.2
  have hS : 0 ≤ ∑ i, ‖Z.s i c x‖ ^ 2 := by positivity
  have hFj : ‖F j x‖ ^ 2 = ‖jac X.A j c x‖ ^ 2 * ‖X.L₂.g j c x‖ ^ 2 *
      (‖X.L.g j c x‖ ^ 2) ^ (D + T) * ‖F c x‖ ^ 2 := by
    rw [hF.2.1 j c x hx, norm_mul, norm_mul, norm_mul, norm_pow]; ring
  have key := exp_identity (D := D) T t _ _ (∑ k, ‖X.e k c x‖ ^ 2) (φA.φ c x) hG hg₂
  rw [hFj, ssum_transform X Z j c x hx, Real.mul_rpow hG.le hS, φA.compat j c x hx]
  unfold fsWeight
  rw [esum_transform X j c x hx, Real.log_mul hG.ne' hE.ne', ← key]
  ring

theorem dens_eq (X : EmbDatum D) (φA : TwistWeight X.A X.L₂ X.L D) (T : ℕ) (t : ℝ)
    (j : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source) (a S : ℝ) :
    a * S ^ (-(t + 1)) * Real.exp (-(φA.φ j x + ((T : ℝ) - 1 - t) * fsWeight X.e j x)) =
      a * Real.exp (-(φA.φ j x + (T : ℝ) * fsWeight X.e j x)) *
        (S ^ (-(t + 1)) * (∑ k, ‖X.e k j x‖ ^ 2) ^ (t + 1)) := by
  have hE := esum_pos X j x hx
  rw [Real.rpow_def_of_pos hE (t + 1)]
  unfold fsWeight
  have : Real.exp (-(φA.φ j x + ((T : ℝ) - 1 - t) * Real.log (∑ k, ‖X.e k j x‖ ^ 2))) =
      Real.exp (-(φA.φ j x + (T : ℝ) * Real.log (∑ k, ‖X.e k j x‖ ^ 2))) *
        Real.exp (Real.log (∑ k, ‖X.e k j x‖ ^ 2) * (t + 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

theorem ratio_le_of_nonpos (t S E r : ℝ) (ht : t + 1 ≤ 0) (hE : 0 < E) (hS : 0 ≤ S)
    (hr : 0 ≤ r) (hSE : S ≤ r * E) :
    S ^ (-(t + 1)) * E ^ (t + 1) ≤ r ^ (-(t + 1)) := by
  have h1 : S ^ (-(t + 1)) ≤ (r * E) ^ (-(t + 1)) := Real.rpow_le_rpow hS hSE (by linarith)
  rw [Real.mul_rpow hr hE.le] at h1
  have hEp : 0 < E ^ (t + 1) := Real.rpow_pos_of_pos hE _
  calc S ^ (-(t + 1)) * E ^ (t + 1) ≤ r ^ (-(t + 1)) * E ^ (-(t + 1)) * E ^ (t + 1) := by gcongr
    _ = r ^ (-(t + 1)) := by
      rw [Real.rpow_neg hE.le, mul_assoc, inv_mul_cancel₀ hEp.ne', mul_one]

theorem ratio_le_of_nonneg (t S E C : ℝ) (ht : 0 ≤ t + 1) (hE : 0 < E) (hS : 0 < S)
    (hSE : E ≤ C * S) :
    S ^ (-(t + 1)) * E ^ (t + 1) ≤ C ^ (t + 1) := by
  have h1 : E / S ≤ C := (div_le_iff₀ hS).mpr hSE
  have h2 : (E / S) ^ (t + 1) ≤ C ^ (t + 1) := Real.rpow_le_rpow (by positivity) h1 ht
  rw [Real.div_rpow hE.le hS.le, div_eq_mul_inv, ← Real.rpow_neg hS.le, mul_comm] at h2
  exact h2

theorem local_bound (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D)
    (T : ℕ) (hDT : D ≤ T) (F : Fin X.A.n → X.U → ℂ) (hF : F ∈ topSections X.A X.L₂ X.L (D + T))
    (hfil : IsFil X.A Z.s F (T - D)) (t : ℝ) (ht : 0 < t + 1) (x₀ : X.U)
    (hx₀ : x₀ ∈ zeroSet X.A Z.s) (c : Fin X.A.n) (hc : c = chartIdx X.A x₀) :
    ∃ ε > (0 : ℝ), ∃ K : ℝ, Metric.ball (X.A.chart c x₀) ε ⊆ (X.A.chart c).target ∧
      ∀ w ∈ Metric.ball (X.A.chart c x₀) ε,
        ENNReal.ofReal (2 ^ D * ‖F c ((X.A.chart c).symm w)‖ ^ 2 *
            (∑ i, ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2) ^ (-(t + 1)) *
            Real.exp (-(φA.φ c ((X.A.chart c).symm w) +
              ((T : ℝ) - 1 - t) * fsWeight X.e c ((X.A.chart c).symm w)))) ≤
          ENNReal.ofReal (K * ‖w - X.A.chart c x₀‖ ^ (2 * ((T : ℝ) - D) - 2 * (t + 1))) := by
  subst hc
  set c := chartIdx X.A x₀
  set w₀ := X.A.chart c x₀
  have hx₀s : x₀ ∈ (X.A.chart c).source := mem_source_chartIdx X.A x₀
  have hw₀t : w₀ ∈ (X.A.chart c).target := (X.A.chart c).map_source hx₀s
  have hsymm : (X.A.chart c).symm w₀ = x₀ := (X.A.chart c).left_inv hx₀s
  have hmem : w₀ ∈ (X.A.chart c).target ∩ (X.A.chart c).symm ⁻¹' (X.A.chart c).source :=
    ⟨hw₀t, by simpa [hsymm] using hx₀s⟩
  have hnhd : (X.A.chart c).target ∩ (X.A.chart c).symm ⁻¹' (X.A.chart c).source ∈ 𝓝 w₀ :=
    ((X.A.chart c).continuousOn_symm.isOpen_inter_preimage (X.A.chart c).open_target
      (X.A.chart c).open_source).mem_nhds hmem

  have hfan : AnalyticAt ℂ (F c ∘ (X.A.chart c).symm) w₀ := hF.1 c c w₀ hmem
  obtain ⟨C₁, hC₁⟩ := exists_bound_of_iteratedFDeriv_eq_zero hfan (T - D)
    (fun k hk => hfil x₀ hx₀ k hk)

  set σ : (Fin D → ℂ) → (Fin D → ℂ) := fun z i => Z.s i c ((X.A.chart c).symm z)
  have hσd : DifferentiableAt ℂ σ w₀ :=
    differentiableAt_pi.mpr fun i => ((s_mem X Z i).1 c c w₀ hmem).differentiableAt
  have hdet : LinearMap.det (fderiv ℂ σ w₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0 :=
    Z.nondeg x₀ hx₀
  have hσ0 : σ w₀ = 0 := funext fun i => by simp only [σ, hsymm]; exact hx₀ i
  obtain ⟨κ, hκ, hκb⟩ := exists_lowerBound_of_det_ne_zero hσd.hasFDerivAt hdet hσ0

  set h : (Fin D → ℂ) → ℝ := fun w => Real.exp (-(φA.φ c ((X.A.chart c).symm w) +
    ((T : ℝ) - 1 - t) * fsWeight X.e c ((X.A.chart c).symm w)))
  have hφc : ContinuousAt (fun w => φA.φ c ((X.A.chart c).symm w)) w₀ :=
    ((φA.smooth c c).continuousOn).continuousAt hnhd
  have hEc : ContinuousAt (fun w => ∑ k, ‖X.e k c ((X.A.chart c).symm w)‖ ^ 2) w₀ := by
    have hk : ∀ k, ContinuousAt (fun w => X.e k c ((X.A.chart c).symm w)) w₀ := fun k =>
      ((X.e_mem k).1 c c w₀ hmem).continuousAt
    exact tendsto_finsetSum Finset.univ fun k _ => (hk k).norm.pow 2
  have hE0 : (∑ k, ‖X.e k c ((X.A.chart c).symm w₀)‖ ^ 2) ≠ 0 := by
    rw [hsymm]; exact (esum_pos X c x₀ hx₀s).ne'
  have hcont : ContinuousAt h w₀ :=
    (hφc.add (continuousAt_const.mul (hEc.log hE0))).neg.rexp
  have hev : ∀ᶠ w in 𝓝 w₀, h w < h w₀ + 1 := hcont.eventually (gt_mem_nhds (lt_add_one _))
  have hall := (show ∀ᶠ w in 𝓝 w₀, w ∈ (X.A.chart c).target from
    (X.A.chart c).open_target.mem_nhds hw₀t).and (hC₁.and (hκb.and hev))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  have hh0 : 0 < h w₀ := Real.exp_pos _
  refine ⟨ε, hε, 2 ^ D * C₁ ^ 2 * (κ ^ 2) ^ (-(t + 1)) * (h w₀ + 1), fun w hw => (hball w hw).1,
    fun w hw => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hball w hw
  apply ENNReal.ofReal_le_ofReal
  have hK : 0 ≤ 2 ^ D * C₁ ^ 2 * (κ ^ 2) ^ (-(t + 1)) * (h w₀ + 1) := by positivity
  by_cases hw0 : w = w₀
  · have hS0 : ∑ i, ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2 = 0 := by
      rw [hw0, hsymm]; simp [show ∀ i, Z.s i c x₀ = 0 from hx₀]
    rw [hS0, Real.zero_rpow (by linarith)]
    simp only [mul_zero, zero_mul]
    exact mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)
  · set r := ‖w - w₀‖ with hr
    have hr0 : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hw0)
    set S := ∑ i, ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2
    have hσS : ‖σ w‖ ≤ Real.sqrt S := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      refine Real.le_sqrt_of_sq_le ?_
      exact Finset.single_le_sum (f := fun i => ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have hS : κ ^ 2 * r ^ 2 ≤ S := by
      have : (κ * r) ^ 2 ≤ (Real.sqrt S) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h2.trans hσS) 2
      rwa [Real.sq_sqrt (by positivity), mul_pow] at this
    have hSr : S ^ (-(t + 1)) ≤ (κ ^ 2 * r ^ 2) ^ (-(t + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hS (by linarith)
    have hF2 : ‖F c ((X.A.chart c).symm w)‖ ^ 2 ≤ (C₁ * r ^ (T - D)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hra : r ^ (2 * ((T : ℝ) - D) - 2 * (t + 1)) =
        (r ^ (T - D)) ^ 2 * (r ^ 2) ^ (-(t + 1)) := by
      rw [← pow_mul, ← Real.rpow_natCast r ((T - D) * 2), ← Real.rpow_two r,
        ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
      congr 1
      push_cast [Nat.cast_sub hDT]
      ring
    calc 2 ^ D * ‖F c ((X.A.chart c).symm w)‖ ^ 2 * S ^ (-(t + 1)) * h w
        ≤ 2 ^ D * (C₁ * r ^ (T - D)) ^ 2 * (κ ^ 2 * r ^ 2) ^ (-(t + 1)) * (h w₀ + 1) := by
          gcongr
      _ = 2 ^ D * C₁ ^ 2 * (κ ^ 2) ^ (-(t + 1)) * (h w₀ + 1) *
            r ^ (2 * ((T : ℝ) - D) - 2 * (t + 1)) := by
          rw [hra, Real.mul_rpow (by positivity) (by positivity)]; ring

end DivisionNearS

end

end GroundTheory.Heights₂.Heights.EffectiveHS
