import Formalism.UnipotentAdelicQuotients.EllipticRegularity.KernDecay
import Formalism.UnipotentAdelicQuotients.EllipticRegularity.KernDil
import Formalism.UnipotentAdelicQuotients.EllipticRegularity.KernDer

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

lemma exists_smooth_ext {d : ℕ} {U : Set (E d)} {a : E d → ℂ} {x0 : E d} (hU : IsOpen U) (hx0 : x0 ∈ U)
    (ha : ContDiffOn ℝ ∞ a U) :
    ∃ r0 > 0, ball x0 (2 * r0) ⊆ U ∧ ∃ b : E d → ℂ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      ∀ x ∈ closedBall x0 (2 * r0), b x = a x := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x0 hx0
  let χ : ContDiffBump x0 := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  refine ⟨R / 4, by positivity, ?_, fun x => ((χ x : ℝ) : ℂ) * a x, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (by linarith)).trans hRU
  · have hsub : tsupport χ ⊆ U := by
      rw [χ.tsupport_eq]
      exact (Metric.closedBall_subset_ball (by show 3 * R / 4 < R; linarith)).trans hRU
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt).mul
        ((ha x hx).contDiffAt (hU.mem_nhds hx))
    · have hx' : x ∉ tsupport χ := fun h => hx (hsub h)
      have hev : (fun x => ((χ x : ℝ) : ℂ) * a x) =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro x hx
    have hx' : x ∈ Metric.closedBall x0 χ.rIn := by
      show x ∈ Metric.closedBall x0 (R / 2)
      exact Metric.closedBall_subset_closedBall (by linarith) hx
    simp [χ.one_of_mem_closedBall hx']

lemma norm_lt_of_psi_ne {d : ℕ} {ψ0 : E d → ℝ} (hψ0s : tsupport ψ0 ⊆ ball 0 2) {r : ℝ} (hr : 0 < r)
    {x x0 : E d} (hz : ψ0 (r⁻¹ • (x - x0)) ≠ 0) : ‖x - x0‖ < 2 * r := by
  have hmem : r⁻¹ • (x - x0) ∈ ball (0 : E d) 2 := hψ0s (subset_tsupport _ hz)
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
  rw [inv_mul_lt_iff₀ hr] at hmem
  linarith

theorem frozenKernelSmall : KernelSmall := by
  intro d U a x0 ψ0 hU hx0 ha hψ hψc hψs
  obtain ⟨r0, hr0, hball, b, hb, hbc, hab⟩ := exists_smooth_ext hU hx0 ha
  have hψC : ContDiff ℝ ∞ (fun y : E d => ((ψ0 y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have hψCc : HasCompactSupport (fun y : E d => ((ψ0 y : ℝ) : ℂ)) := hψc.comp_left Complex.ofReal_zero
  set n := Module.finrank ℝ (E d) + 1 with hn
  obtain ⟨K, hK⟩ := derivL1Norm_rescaled_difference_le (fun y => ((ψ0 y : ℝ) : ℂ)) hψC hψCc b hb hbc x0 r0 n
  set I := ∫⁻ w : E d, ENNReal.ofReal ((1 + ‖w‖) ^ (-((n : ℕ) : ℝ))) with hIdef
  have hI : I < ⊤ := finite_integral_one_add_norm (by rw [hn]; push_cast; linarith)
  let c : ℝ → E d → ℂ := fun r y => ((ψ0 y : ℝ) : ℂ) * (b (x0 + r • y) - b x0)
  have hcs : ∀ r, ContDiff ℝ ∞ (c r) := fun r =>
    hψC.mul ((hb.comp (contDiff_const.add (contDiff_id.const_smul r))).sub contDiff_const)
  have hcc : ∀ r, HasCompactSupport (c r) := fun r => hψCc.mul_right
  have hf_eq : ∀ r : ℝ, 0 < r → r ≤ r0 →
      (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (a x - a x0)) = fun x => c r (r⁻¹ • (x - x0)) := by
    intro r hr hrr
    funext x
    have hx : x0 + r • (r⁻¹ • (x - x0)) = x := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
    simp only [c, hx]
    by_cases hz : ψ0 (r⁻¹ • (x - x0)) = 0
    · simp [hz]
    · have hlt := norm_lt_of_psi_ne hψs hr hz
      have hxm : x ∈ closedBall x0 (2 * r0) := by
        rw [mem_closedBall, dist_eq_norm]; linarith
      rw [hab x hxm, hab x0 (mem_closedBall_self (by linarith))]
  refine ⟨r0, hr0, (2 ^ n * (1 + 2 ^ n)) * K * I.toReal, hball, fun r hr hrr => ⟨?_, fun N => ?_⟩⟩
  · rw [hf_eq r hr hrr]
    have h2 := hK r hr hrr
    have hKr : 0 ≤ K * r := (derivL1Norm_nonneg _ _).trans h2
    have hA : (0 : ℝ) ≤ 2 ^ n * (1 + 2 ^ n) := by positivity
    have hAKr : 0 ≤ 2 ^ n * (1 + 2 ^ n) * K * r := by
      rw [mul_assoc]; exact mul_nonneg hA hKr
    have hpt : ∀ ζ : E d, ‖𝓕 (fun x => c r (r⁻¹ • (x - x0))) ζ‖ₑ ≤
        ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * r) *
          ENNReal.ofReal (r ^ Module.finrank ℝ (E d) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) := by
      intro ζ
      rw [← ofReal_norm, norm_fourier_comp_dil _ r hr x0 ζ, ← ENNReal.ofReal_mul hAKr]
      apply ENNReal.ofReal_le_ofReal
      have h1 := norm_fourier_le_rpow (hcs r) (hcc r) n (r • ζ)
      have hW : 0 ≤ (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
      have hrd : 0 ≤ r ^ Module.finrank ℝ (E d) := by positivity
      calc r ^ Module.finrank ℝ (E d) * ‖𝓕 (c r) (r • ζ)‖
          ≤ r ^ Module.finrank ℝ (E d) *
              (2 ^ n * (1 + 2 ^ n) * derivL1Norm (c r) n * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 hrd
        _ ≤ r ^ Module.finrank ℝ (E d) *
              (2 ^ n * (1 + 2 ^ n) * (K * r) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) := by
            gcongr
        _ = 2 ^ n * (1 + 2 ^ n) * K * r *
              (r ^ Module.finrank ℝ (E d) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) := by ring
    calc (∫⁻ ζ, ‖𝓕 (fun x => c r (r⁻¹ • (x - x0))) ζ‖ₑ)
        ≤ ∫⁻ ζ : E d, ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * r) *
          ENNReal.ofReal (r ^ Module.finrank ℝ (E d) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * r) * I := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_dil_weight r hr _ (by rw [hn]; push_cast; linarith)]
      _ = ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * I.toReal * r) := by
          rw [← ENNReal.ofReal_toReal hI.ne, ← ENNReal.ofReal_mul hAKr, ENNReal.toReal_ofReal
            ENNReal.toReal_nonneg]
          ring_nf
  · rw [hf_eq r hr hrr]
    have hsm : ContDiff ℝ ∞ (fun x => c r (r⁻¹ • (x - x0))) :=
      (hcs r).comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
    have hsc : HasCompactSupport (fun x => c r (r⁻¹ • (x - x0))) :=
      (hcc r).comp_homeomorph ((Homeomorph.subRight x0).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')))
    refine lt_of_le_of_lt (lintegral_mono fun ζ => ?_) (lintegral_weight_fourier_lt_top hsm hsc ⌈N + 1⌉₊)
    gcongr
    have h1 : 1 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
    calc ‖ζ‖ * (1 + ‖ζ‖) ^ N ≤ (1 + ‖ζ‖) ^ (1 : ℝ) * (1 + ‖ζ‖) ^ N := by
          rw [Real.rpow_one]; gcongr; linarith
      _ = (1 + ‖ζ‖) ^ (N + 1) := by rw [← Real.rpow_add (by linarith)]; ring_nf
      _ ≤ (1 + ‖ζ‖) ^ ((⌈N + 1⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
      _ = (1 + ‖ζ‖) ^ ⌈N + 1⌉₊ := Real.rpow_natCast _ _

end

end ZetaZeros.D.EllReg
