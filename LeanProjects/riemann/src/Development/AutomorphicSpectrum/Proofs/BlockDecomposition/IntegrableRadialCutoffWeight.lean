import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi

noncomputable section

open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.PerUInt.Outer

theorem integrable_rpow_abs_mul_phi (τ : ℝ) (hτ : 0 ≤ τ) (h1 : τ < 1) :
    Integrable (fun x : ℝ => |x| ^ (-τ) * phi x) := by
  have hI : IntegrableOn (fun x : ℝ => x ^ (-τ)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = indicator (Ioc 0 1) (fun x : ℝ => x ^ (-τ)) := ⟨_, rfl⟩
  have hG : Integrable G := hGdef ▸ hI.integrable_indicator measurableSet_Ioc
  have hG' : Integrable (fun x => G (-x)) := hG.comp_neg
  have hGn : ∀ y, 0 ≤ G y := by
    intro y
    rw [hGdef]
    refine indicator_nonneg (fun x hx => Real.rpow_nonneg hx.1.le _) y
  have hD : Integrable (fun x => G x + G (-x) + phi x) := (hG.add hG').add integrable_phi
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by
    simpa [ae_iff] using (measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0)
  refine hD.mono' ((continuous_abs.measurable.pow_const (-τ)).mul measurable_phi).aestronglyMeasurable ?_
  filter_upwards [h0] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg x) _) (phi_nonneg x))]
  have hp0 := phi_nonneg x
  have hp1 := phi_le_one x
  have hr0 : 0 ≤ |x| ^ (-τ) := Real.rpow_nonneg (abs_nonneg x) _
  have hGx := hGn x
  have hGnx := hGn (-x)
  by_cases hx1 : |x| ≤ 1
  · have hle : |x| ^ (-τ) * phi x ≤ |x| ^ (-τ) := mul_le_of_le_one_right hr0 hp1
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hm : -x ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by rwa [abs_of_neg hneg] at hx1⟩
      have : G (-x) = |x| ^ (-τ) := by
        rw [hGdef, indicator_of_mem hm, abs_of_neg hneg]
      linarith
    · have hm : x ∈ Ioc (0 : ℝ) 1 := ⟨hpos, by rwa [abs_of_pos hpos] at hx1⟩
      have : G x = |x| ^ (-τ) := by
        rw [hGdef, indicator_of_mem hm, abs_of_pos hpos]
      linarith
  · have hge : 1 ≤ |x| := (not_le.1 hx1).le
    have h2 : |x| ^ (-τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hge (by linarith)
    have h3 : |x| ^ (-τ) * phi x ≤ phi x := mul_le_of_le_one_left hp0 h2
    linarith

theorem rpow_anti {x y r : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hr : r ≤ 0) : y ^ r ≤ x ^ r :=
  Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hr (mem_Ioi.2 hx) (mem_Ioi.2 (hx.trans_le hxy)) hxy

theorem rpow_bound (σ a b : ℝ) (hσ : 0 < σ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a ^ 2 + b ^ 2) ^ (-1 - σ / 2) * ((a ^ 2 + b ^ 2) / max |a| |b|) ≤
      |a| ^ (-((1 + σ) / 2)) * |b| ^ (-((1 + σ) / 2)) := by
  have hA : 0 < |a| := abs_pos.2 ha
  have hB : 0 < |b| := abs_pos.2 hb
  have hma : |a| ≤ max |a| |b| := le_max_left _ _
  have hmb : |b| ≤ max |a| |b| := le_max_right _ _
  have hc : (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases max_choice |a| |b| with h | h
    · rw [h, sq_abs]; nlinarith [sq_nonneg b]
    · rw [h, sq_abs]; nlinarith [sq_nonneg a]
  generalize max |a| |b| = m at hma hmb hc ⊢
  generalize a ^ 2 + b ^ 2 = c at hc ⊢
  have hm : 0 < m := lt_of_lt_of_le hA hma
  have hm2 : 0 < m ^ 2 := pow_pos hm 2
  have hc0 : 0 < c := lt_of_lt_of_le hm2 hc
  have e1 : c ^ (-1 - σ / 2) * (c / m) = c ^ (-(σ / 2)) / m := by
    have h : c ^ (-(σ / 2)) = c ^ (-1 - σ / 2) * c := by
      rw [show -(σ / 2) = (-1 - σ / 2) + 1 by ring, Real.rpow_add hc0, Real.rpow_one]
    rw [h]
    ring
  have e2 : c ^ (-(σ / 2)) ≤ (m ^ 2) ^ (-(σ / 2)) :=
    rpow_anti hm2 hc (by linarith)
  have e3 : (m ^ 2) ^ (-(σ / 2)) / m = m ^ (-((1 + σ) / 2)) * m ^ (-((1 + σ) / 2)) := by
    rw [← Real.rpow_natCast m 2, ← Real.rpow_mul hm.le, ← Real.rpow_add hm,
      ← Real.rpow_sub_one hm.ne']
    congr 1
    push_cast
    ring
  have e4 : m ^ (-((1 + σ) / 2)) ≤ |a| ^ (-((1 + σ) / 2)) :=
    rpow_anti hA hma (by linarith)
  have e5 : m ^ (-((1 + σ) / 2)) ≤ |b| ^ (-((1 + σ) / 2)) :=
    rpow_anti hB hmb (by linarith)
  have hmr : 0 ≤ m ^ (-((1 + σ) / 2)) := Real.rpow_nonneg hm.le _
  calc c ^ (-1 - σ / 2) * (c / m) = c ^ (-(σ / 2)) / m := e1
    _ ≤ (m ^ 2) ^ (-(σ / 2)) / m := div_le_div_of_nonneg_right e2 hm.le
    _ = m ^ (-((1 + σ) / 2)) * m ^ (-((1 + σ) / 2)) := e3
    _ ≤ |a| ^ (-((1 + σ) / 2)) * |b| ^ (-((1 + σ) / 2)) :=
      mul_le_mul e4 e5 hmr (Real.rpow_nonneg hA.le _)

theorem integrable_firstColumn : ∀ σ : ℝ, 0 < σ → σ < 1 → Integrable (fun p : ℝ × ℝ =>
    (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - σ / 2) * ((p.1 ^ 2 + p.2 ^ 2) / max |p.1| |p.2|) *
      (phi p.1 * phi p.2)) := by
  intro σ h0 h1
  have hg := integrable_rpow_abs_mul_phi ((1 + σ) / 2) (by linarith) (by linarith)
  have hP : Integrable (fun p : ℝ × ℝ =>
      (|p.1| ^ (-((1 + σ) / 2)) * phi p.1) * (|p.2| ^ (-((1 + σ) / 2)) * phi p.2)) := by
    rw [Measure.volume_eq_prod]
    exact hg.mul_prod hg
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
    simpa [ae_iff] using (measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0)
  have hne1 : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hne
  have hne2 : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae hne
  have hc : Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) :=
    (measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)
  have hmx : Measurable (fun p : ℝ × ℝ => max |p.1| |p.2|) :=
    (continuous_abs.measurable.comp measurable_fst).max
      (continuous_abs.measurable.comp measurable_snd)
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - σ / 2) * ((p.1 ^ 2 + p.2 ^ 2) / max |p.1| |p.2|) *
        (phi p.1 * phi p.2)) :=
    ((hc.pow_const _).mul (hc.div hmx)).mul
      ((measurable_phi.comp measurable_fst).mul (measurable_phi.comp measurable_snd))
  refine hP.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [hne1, hne2] with p hp1 hp2
  have hc0 : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
  have hm0 : 0 ≤ max |p.1| |p.2| := le_max_of_le_left (abs_nonneg _)
  have hph : 0 ≤ phi p.1 * phi p.2 := mul_nonneg (phi_nonneg _) (phi_nonneg _)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hc0 _) (div_nonneg hc0 hm0)) hph)]
  calc _ ≤ (|p.1| ^ (-((1 + σ) / 2)) * |p.2| ^ (-((1 + σ) / 2))) * (phi p.1 * phi p.2) :=
        mul_le_mul_of_nonneg_right (rpow_bound σ p.1 p.2 h0 hp1 hp2) hph
    _ = _ := by ring

end GlobalTheory.CompanionTheory.PerUInt.Outer
