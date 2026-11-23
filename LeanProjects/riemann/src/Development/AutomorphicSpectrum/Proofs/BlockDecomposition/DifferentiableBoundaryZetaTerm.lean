import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem Bd_differentiable : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
    Set0 μ 𝓕 mK 𝓓 → Aut H → Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c) := by
  intro μ 𝓕 mK 𝓓 H c h0 hH s₀
  obtain ⟨C, hC⟩ := hH.bdd
  have hband : MeasurableSet band :=
    (measurable_Dt measurableSet_Ici).inter (measurable_Dt measurableSet_Iio)
  have hS : MeasurableSet (𝓕 ∩ band) := h0.meas.inter hband
  haveI : IsFiniteMeasure (μ.restrict (𝓕 ∩ band)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact h0.vol⟩
  set R : ℝ := |s₀.re| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)

  have hpow : ∀ g ∈ 𝓕 ∩ band, ∀ s ∈ Metric.ball s₀ 1, ‖((Dt g : ℝ) : ℂ) ^ s‖ ≤ (2 : ℝ) ^ R := by
    intro g hg s hs
    obtain ⟨h1, h2⟩ := hg.2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
    have hre : s.re ≤ R := by
      have h3 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
      have h4 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      have h5 := abs_le.1 h3
      have h6 := le_abs_self s₀.re
      simp only [Complex.sub_re] at h5
      rw [hR]; linarith [h5.2]
    calc Dt g ^ s.re ≤ Dt g ^ R := Real.rpow_le_rpow_of_exponent_le h1 hre
      _ ≤ (2 : ℝ) ^ R := Real.rpow_le_rpow (Dt_pos g).le h2.le hR0
  have hlog : ∀ g ∈ 𝓕 ∩ band, ‖Complex.log ((Dt g : ℝ) : ℂ)‖ ≤ 1 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hg.2
    rw [← Complex.ofReal_log (Dt_pos g).le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg h1)]
    linarith [Real.log_le_sub_one_of_pos (Dt_pos g)]
  have hF' : ∀ s : ℂ, Measurable fun g =>
      H g * cdet c g * (((Dt g : ℝ) : ℂ) ^ s * Complex.log ((Dt g : ℝ) : ℂ)) := by
    intro s
    have hl : Measurable fun g => Complex.log ((Dt g : ℝ) : ℂ) :=
      Complex.measurable_log.comp (Complex.measurable_ofReal.comp measurable_Dt)
    exact (hH.cont.measurable.mul (measurable_cdet c)).mul
      (((Complex.measurable_ofReal.comp measurable_Dt).pow_const s).mul hl)
  have hbd : ∀ g ∈ 𝓕 ∩ band, ∀ s ∈ Metric.ball s₀ 1, ‖H g * cdet c g * ((((Dt g : ℝ) : ℂ) ^ s) * Complex.log ((Dt g : ℝ) : ℂ))‖ ≤ C * (2 : ℝ) ^ R := by
    intro g hg s hs
    rw [norm_mul, norm_mul, norm_mul, norm_cdet, mul_one]
    have h1 := hpow g hg s hs
    have h2 := hlog g hg
    have h3 := hC g
    calc ‖H g‖ * (‖((Dt g : ℝ) : ℂ) ^ s‖ * ‖Complex.log ((Dt g : ℝ) : ℂ)‖)
        ≤ C * ((2 : ℝ) ^ R * 1) := by gcongr
      _ = C * (2 : ℝ) ^ R := by ring
  have hint : Integrable (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s₀) (μ.restrict (𝓕 ∩ band)) := by
    refine (integrable_const (C * (2 : ℝ) ^ R)).mono' (measurable_w hH c s₀).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun g hg => ?_)
    rw [norm_mul, norm_mul, norm_cdet, mul_one]
    have h1 := hpow g hg s₀ (Metric.mem_ball_self one_pos)
    have h3 := hC g
    gcongr
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict (𝓕 ∩ band))
    (F := fun s g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s)
    (F' := fun s g => H g * cdet c g * (((Dt g : ℝ) : ℂ) ^ s * Complex.log ((Dt g : ℝ) : ℂ)))
    (x₀ := s₀) (s := Metric.ball s₀ 1) (bound := fun _ => C * (2 : ℝ) ^ R)
    (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (measurable_w hH c s).aestronglyMeasurable)
    hint (hF' s₀).aestronglyMeasurable
    ((ae_restrict_iff' hS).2 (Eventually.of_forall fun g hg s hs => hbd g hg s hs))
    (integrable_const _)
    (Eventually.of_forall fun g s _ => by
      have := ((hasDerivAt_id s).const_cpow (c := ((Dt g : ℝ) : ℂ)) (Or.inl (Dt_ne g))).const_mul (H g * cdet c g)
      simpa using this)
  exact key.2.differentiableAt

end GlobalTheory.CompanionTheory.RSZeta
