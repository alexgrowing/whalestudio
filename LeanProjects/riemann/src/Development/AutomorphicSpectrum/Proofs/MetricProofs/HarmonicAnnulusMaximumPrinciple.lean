import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem harmonic_eventually_eq_of_ball_le {h : ℂ → ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : InnerProductSpace.HarmonicOnNhd h (Metric.ball z₀ r))
    (hle : ∀ z ∈ Metric.ball z₀ r, h z ≤ h z₀) : ∀ᶠ z in 𝓝 z₀, h z = h z₀ := by
  obtain ⟨F, hF, hre⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hh
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hball : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  have hnorm : ∀ z ∈ Metric.ball z₀ r, ‖Complex.exp (F z)‖ = Real.exp (h z) := fun z hz => by
    rw [Complex.norm_exp]
    exact congrArg Real.exp (hre hz)
  have hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz
    exact (hF z hz).differentiableAt.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (F z)) z₀ := by
    filter_upwards [hball] with z hz
    simp only [Function.comp_apply]
    rw [hnorm z hz, hnorm z₀ hz₀]
    exact Real.exp_le_exp.2 (hle z hz)
  filter_upwards [Complex.eventually_eq_of_isLocalMax_norm hdiff hmax, hball] with z hz hzb
  have h1 := congrArg norm hz
  rw [hnorm z hzb, hnorm z₀ hz₀] at h1
  exact Real.exp_injective h1

theorem harmonic_annulus_le_zero : ∀ (h : ℂ → ℝ) (a b : ℝ), 0 < a → a < b →
    ContinuousOn h {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} →
    (∀ z : ℂ, a < ‖z‖ → ‖z‖ < b → InnerProductSpace.HarmonicAt h z) →
    (∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → h z ≤ 0) →
    ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → h z ≤ 0 := by
  intro h a b ha hab hc hh hb z hz1 hz2
  by_contra hpos
  push Not at hpos
  set K : Set ℂ := {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} with hK
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hKcomp : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset hKclosed
      (fun w hw => by simpa using hw.2)
  have hzK : z ∈ K := ⟨hz1, hz2⟩
  obtain ⟨z₁, hz₁K, hz₁⟩ := hKcomp.exists_isMaxOn ⟨z, hzK⟩ hc
  set S : Set ℂ := K ∩ h ⁻¹' {h z₁} with hS
  have hSclosed : IsClosed S :=
    hc.preimage_isClosed_of_isClosed hKclosed isClosed_singleton
  have hScomp : IsCompact S := hKcomp.of_isClosed_subset hSclosed Set.inter_subset_left
  obtain ⟨z₀, hz₀S, hz₀⟩ :=
    hScomp.exists_isMaxOn ⟨z₁, hz₁K, rfl⟩ (continuous_norm.continuousOn (s := S))
  have hz₀K : z₀ ∈ K := hz₀S.1
  have hval : h z₀ = h z₁ := hz₀S.2
  have hMpos : 0 < h z₀ := hval ▸ hpos.trans_le (hz₁ hzK)
  have hlo : a < ‖z₀‖ := lt_of_le_of_ne hz₀K.1 fun e => absurd (hb z₀ (Or.inl e.symm)) (not_le.2 hMpos)
  have hhi : ‖z₀‖ < b := lt_of_le_of_ne hz₀K.2 fun e => absurd (hb z₀ (Or.inr e)) (not_le.2 hMpos)
  have hUopen : IsOpen {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUopen z₀ ⟨hlo, hhi⟩
  have hloc : ∀ᶠ w in 𝓝 z₀, h w = h z₀ := by
    refine harmonic_eventually_eq_of_ball_le hr (fun w hw => hh w (hrU hw).1 (hrU hw).2) ?_
    intro w hw
    rw [hval]
    exact hz₁ ⟨(hrU hw).1.le, (hrU hw).2.le⟩
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1
    (hloc.and (hUopen.mem_nhds ⟨hlo, hhi⟩))
  have hz₀pos : 0 < ‖z₀‖ := ha.trans hlo

  set t : ℝ := ε / (2 * ‖z₀‖) with ht
  have htpos : 0 < t := by positivity
  set w : ℂ := ((1 + t : ℝ) : ℂ) * z₀ with hw
  have hwnorm : ‖w‖ = (1 + t) * ‖z₀‖ := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hdist : dist w z₀ < ε := by
    have e : w - z₀ = (t : ℂ) * z₀ := by
      rw [hw]; push_cast; ring
    rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le, ht]
    have : ε / (2 * ‖z₀‖) * ‖z₀‖ = ε / 2 := by field_simp
    rw [this]
    linarith
  obtain ⟨hwval, hwU⟩ := hεb w hdist
  have hwS : w ∈ S := ⟨⟨hwU.1.le, hwU.2.le⟩, by simpa [hval] using hwval⟩
  have hle : ‖w‖ ≤ ‖z₀‖ := hz₀ hwS
  rw [hwnorm] at hle
  nlinarith [mul_pos htpos hz₀pos]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
