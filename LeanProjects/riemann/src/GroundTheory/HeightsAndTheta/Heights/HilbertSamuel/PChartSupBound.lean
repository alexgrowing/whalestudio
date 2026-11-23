import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolydiscSubmean
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartTaylorCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric

noncomputable section

theorem ChartSupBound.proof : ChartSupBound.Statement := by
  intro D V K ψ ν hV hK hKV hψ hν hν0
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, fun n _ F _ w hw => by simp [hKe] at hw⟩
  obtain ⟨r, hr0, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  set S := cthickening r K with hS
  have hSc : IsCompact S := hK.cthickening
  have hSne : S.Nonempty := hKne.mono (self_subset_cthickening K)

  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ M := by
    have h1 := hψ.fderiv_of_isOpen hV (m := 1) (by norm_num)
    exact hSc.exists_bound_of_continuousOn ((h1.continuousOn_fderiv_of_isOpen hV le_rfl).mono hrV)
  set M' := |M| with hM'

  obtain ⟨x₀, hx₀, hmin⟩ := hSc.exists_isMinOn hSne (hν.mono hrV)
  set ν₀ := ν x₀ with hν₀
  have hν₀pos : 0 < ν₀ := hν0 x₀ (hrV hx₀)
  set P : ℝ := (Real.pi * r ^ 2) ^ D with hP
  have hPpos : 0 < P := by positivity
  have hprod : ∏ _j : Fin D, gaussDiscMass 0 r = P := by
    rw [hP, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp [gaussDiscMass]
  refine ⟨Real.exp (M' * r ^ 2) / (ν₀ * P), fun n hn F hF w hw => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  set s := r / Real.sqrt n with hs
  have hs2 : (n : ℝ) * s ^ 2 = r ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hnpos.le]
    field_simp
  have hsr : s ≤ r := by
    rw [hs]
    refine div_le_self hr0.le ?_
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  set B := closedBall (0 : Fin D → ℂ) s with hB
  have hzS : ∀ z ∈ B, closedBall w ‖z‖ ⊆ S := fun z hz =>
    (closedBall_subset_closedBall ((mem_closedBall_zero_iff.1 hz).trans hsr)).trans
      (closedBall_subset_cthickening hw r)
  have hwzS : ∀ z ∈ B, w + z ∈ S := fun z hz => hzS z hz (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left])

  set ℓ := fderiv ℝ ψ w with hℓ
  set lam : (Fin D → ℂ) →L[ℂ] ℂ := StrongDual.extendRCLike (𝕜 := ℂ) ℓ with hlam
  have hre : ∀ z, (lam z).re = ℓ z := fun z => by
    rw [hlam, StrongDual.extendRCLike_apply]
    simp
  set G : (Fin D → ℂ) → ℂ := fun z => F (w + z) * Complex.exp (((-(n : ℝ) / 2 : ℝ) : ℂ) * lam z)
    with hGdef
  have hG0 : G 0 = F w := by simp [hGdef]
  have hGan : AnalyticOnNhd ℂ G B := by
    intro z hz
    have haff : AnalyticAt ℂ (fun z : Fin D → ℂ => w + z) z := analyticAt_const.add analyticAt_id
    exact ((hF _ (hrV (hwzS z hz))).comp_of_eq haff rfl).mul
      ((analyticAt_const.mul (lam.analyticAt z)).cexp)
  have hPn := PolydiscSubmean.proof D n (fun _ => 0) r G (by omega) hr0 (fun _ => le_rfl) hGan
  simp only [zero_mul, Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at hPn
  rw [hG0, hprod] at hPn
  set k : ℝ := ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) with hk
  have hk0 : 0 ≤ k := by positivity

  have hpt : ∀ z ∈ B, ENNReal.ofReal (k * ‖G z‖ ^ 2) ≤
      ENNReal.ofReal (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) * ν (w + z)) := by
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    have hGz : ‖G z‖ ^ 2 = ‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z) := by
      simp only [hGdef]
      rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, hre, mul_pow, sq (Real.exp _),
        ← Real.exp_add]
      congr 2
      ring
    have hT := ChartTaylorCover.taylor_le hV hψ ((hzS z hz).trans hrV)
      (fun x hx => (hM x (hzS z hz hx)).trans (le_abs_self M))
    have hz' : ‖z‖ ≤ s := mem_closedBall_zero_iff.1 hz
    have hnz : (n : ℝ) * (M' * ‖z‖ ^ 2) ≤ M' * r ^ 2 := by
      calc (n : ℝ) * (M' * ‖z‖ ^ 2) = M' * ((n : ℝ) * ‖z‖ ^ 2) := by ring
        _ ≤ M' * ((n : ℝ) * s ^ 2) := by gcongr
        _ = M' * r ^ 2 := by rw [hs2]
    have hexp : Real.exp (-(M' * r ^ 2)) * (Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(n : ℝ) * ℓ z)) ≤
        Real.exp (-(n : ℝ) * ψ (w + z)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hT hnpos.le
      nlinarith
    have hνz : ν₀ ≤ ν (w + z) := isMinOn_iff.1 hmin _ (hwzS z hz)
    rw [hGz, hk]
    have hF0 : 0 ≤ ‖F (w + z)‖ ^ 2 := by positivity
    calc ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) *
          (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z))
        = ‖F (w + z)‖ ^ 2 * (Real.exp (-(M' * r ^ 2)) *
            (Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(n : ℝ) * ℓ z))) * ν₀ := by ring
      _ ≤ ‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) * ν (w + z) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp hF0) hνz hν₀pos.le (by positivity)

  have hΦ : MeasurePreserving (fun z : Fin D → ℂ => w + z) volume volume :=
    measurePreserving_add_left volume w
  have hemb : MeasurableEmbedding (fun z : Fin D → ℂ => w + z) :=
    (Homeomorph.addLeft w).isClosedEmbedding.measurableEmbedding
  have hint : ENNReal.ofReal (∫ z in B, ‖G z‖ ^ 2) ≤ ∫⁻ z in B, ENNReal.ofReal (‖G z‖ ^ 2) := by
    calc _ ≤ ‖∫ z in B, ‖G z‖ ^ 2‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ z in B, ‖‖G z‖ ^ 2‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = _ := lintegral_congr fun z => Real.enorm_eq_ofReal (by positivity)
  have hmain : ENNReal.ofReal (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) ≤
      ∫⁻ z in V, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(n : ℝ) * ψ z) * ν z) := by
    calc _ ≤ ENNReal.ofReal (k * ∫ z in B, ‖G z‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hPn hk0)
      _ = ENNReal.ofReal k * ENNReal.ofReal (∫ z in B, ‖G z‖ ^ 2) := ENNReal.ofReal_mul hk0
      _ ≤ ENNReal.ofReal k * ∫⁻ z in B, ENNReal.ofReal (‖G z‖ ^ 2) := by gcongr
      _ = ∫⁻ z in B, ENNReal.ofReal k * ENNReal.ofReal (‖G z‖ ^ 2) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ z in B, ENNReal.ofReal (k * ‖G z‖ ^ 2) :=
          lintegral_congr fun z => (ENNReal.ofReal_mul hk0).symm
      _ ≤ ∫⁻ z in B, ENNReal.ofReal (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) *
            ν (w + z)) :=
          setLIntegral_mono' isClosed_closedBall.measurableSet hpt
      _ = ∫⁻ y in (fun z : Fin D → ℂ => w + z) '' B,
            ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ν y) :=
          hΦ.setLIntegral_comp_emb hemb
            (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ν y)) B
      _ ≤ _ := lintegral_mono_set (image_subset_iff.2 fun z hz => hrV (hwzS z hz))
  have hC0 : 0 ≤ Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D := by positivity
  have heq : Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D *
      (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) = ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
    have hnD : (n : ℝ) ^ D ≠ 0 := by positivity
    have he : Real.exp (M' * r ^ 2) * Real.exp (-(M' * r ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hνP : ν₀ * P ≠ 0 := by positivity
    rw [hk, div_eq_mul_inv]
    calc Real.exp (M' * r ^ 2) * (ν₀ * P)⁻¹ * (n : ℝ) ^ D *
          (ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) *
            (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P))
        = (Real.exp (M' * r ^ 2) * Real.exp (-(M' * r ^ 2))) * ((n : ℝ) ^ D * ((n : ℝ) ^ D)⁻¹) *
            ((ν₀ * P) * (ν₀ * P)⁻¹) * (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w)) := by ring
      _ = ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
        rw [he, mul_inv_cancel₀ hnD, mul_inv_cancel₀ hνP]; ring
  calc ENNReal.ofReal (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w))
      = ENNReal.ofReal (Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D) *
          ENNReal.ofReal (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) := by
        rw [← ENNReal.ofReal_mul hC0, heq]
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
