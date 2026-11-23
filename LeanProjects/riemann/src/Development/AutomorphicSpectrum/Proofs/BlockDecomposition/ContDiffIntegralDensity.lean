import Mathlib

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothParam

variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def pderiv (H : P × Y → F) : P × Y → (P →L[ℝ] F) :=
  fun z => fderiv ℝ (fun q => H (q, z.2)) z.1

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
lemma hasFDerivAt_partial {H : P × Y → F} (hH : Differentiable ℝ H) (p : P) (y : Y) :
    HasFDerivAt (fun q => H (q, y))
      ((fderiv ℝ H (p, y)).comp (ContinuousLinearMap.inl ℝ P Y)) p :=
  (hH (p, y)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p y)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
lemma pderiv_eq {H : P × Y → F} (hH : Differentiable ℝ H) :
    pderiv H = fun z => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P Y) := by
  funext z
  exact (hasFDerivAt_partial hH z.1 z.2).fderiv

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y] in
lemma contDiff_pderiv {H : P × Y → F} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (pderiv H) := by
  rw [pderiv_eq (hH.differentiable (by simp))]
  have h1 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  exact h1.clm_comp contDiff_const

omit [FiniteDimensional ℝ P] [NormedSpace ℝ P] [FiniteDimensional ℝ Y] [NormedSpace ℝ Y] in
lemma integrable_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) {H : P × Y → F} (hH : Continuous H) (p : P) :
    Integrable (fun x => u x • H (p, ψ x)) ν := by
  obtain ⟨C, hC⟩ := (isCompact_singleton.prod hK).exists_bound_of_continuousOn
    (f := H) (s := {p} ×ˢ K) hH.continuousOn
  have hc : Continuous fun y => H (p, y) := hH.comp (by fun_prop)
  have meas : AEStronglyMeasurable (fun x => u x • H (p, ψ x)) ν :=
    hu.aestronglyMeasurable.smul (hc.comp_aestronglyMeasurable hψ)
  refine (hu.norm.mul_const C).mono' meas ?_
  filter_upwards [hψK] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC _ ⟨rfl, hx⟩) (norm_nonneg _)

theorem hasFDerivAt_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) [CompleteSpace F] {H : P × Y → F} (hH : ContDiff ℝ ∞ H) (p₀ : P) :
    HasFDerivAt (fun p => ∫ x, u x • H (p, ψ x) ∂ν)
      (∫ x, u x • pderiv H (p₀, ψ x) ∂ν) p₀ := by
  have hd : Differentiable ℝ H := hH.differentiable (by simp)
  have hc' : Continuous (pderiv H) := (contDiff_pderiv hH).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hK).exists_bound_of_continuousOn
    (f := pderiv H) hc'.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p x => u x • H (p, ψ x)) (F' := fun p x => u x • pderiv H (p, ψ x))
    (bound := fun x => ‖u x‖ * C) (s := Metric.closedBall p₀ 1)
    (Metric.closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun p =>
      (integrable_weight hu hψ hK hψK hH.continuous p).aestronglyMeasurable
  · exact integrable_weight hu hψ hK hψK hH.continuous p₀
  · exact (integrable_weight hu hψ hK hψK hc' p₀).aestronglyMeasurable
  · filter_upwards [hψK] with x hx p hp
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ ⟨hp, hx⟩) (norm_nonneg _)
  · exact hu.norm.mul_const C
  · refine Eventually.of_forall fun x p _ => ?_
    have h1 : HasFDerivAt (fun q => H (q, ψ x)) (pderiv H (p, ψ x)) p :=
      ((hasFDerivAt_partial hd p (ψ x)).differentiableAt).hasFDerivAt
    exact h1.const_smul (u x)

theorem contDiff_weight_nat {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (H : P × Y → F),
      ContDiff ℝ ∞ H → ContDiff ℝ n (fun p => ∫ x, u x • H (p, ψ x) ∂ν) := by
  induction n with
  | zero =>
    intro F _ _ _ H hH
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun p =>
      (hasFDerivAt_weight hu hψ hK hψK hH p).continuousAt
  | succ n ih =>
    intro F _ _ _ H hH
    have hfd : fderiv ℝ (fun p => ∫ x, u x • H (p, ψ x) ∂ν)
        = fun p => ∫ x, u x • pderiv H (p, ψ x) ∂ν := by
      funext p
      exact (hasFDerivAt_weight hu hψ hK hψK hH p).fderiv
    have : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [this, contDiff_succ_iff_fderiv]
    refine ⟨fun p => (hasFDerivAt_weight hu hψ hK hψK hH p).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih (P →L[ℝ] F) (pderiv H) (contDiff_pderiv hH)

theorem contDiff_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) [CompleteSpace F] {H : P × Y → F} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p => ∫ x, u x • H (p, ψ x) ∂ν) :=
  contDiff_infty.2 fun n => contDiff_weight_nat hu hψ hK hψK n F H hH

theorem contDiff_integral_density (Ω P Y : Type) [MeasurableSpace Ω] [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (ν : Measure Ω) (w : Ω → ℂ) (ψ : Ω → Y) (K : Set Y)
    (hw : Integrable w ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (h : P × Y → ℂ) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p => ∫ x, h (p, ψ x) * w x ∂ν) ∧
      ∀ p v, fderiv ℝ (fun q => ∫ x, h (q, ψ x) * w x ∂ν) p v
        = ∫ x, fderiv ℝ (fun q => h (q, ψ x)) p v * w x ∂ν := by
  have hu₁ : Integrable (fun x => (w x).re) ν := hw.re
  have hu₂ : Integrable (fun x => (w x).im) ν := hw.im
  set h₂ : P × Y → ℂ := fun z => Complex.I * h z with hh₂def
  have hh₂ : ContDiff ℝ ∞ h₂ := contDiff_const.mul hh
  have hdec : ∀ (a b : ℂ), a * b = b.re • a + b.im • (Complex.I * a) := by
    intro a b
    apply Complex.ext <;> simp <;> ring
  have hsplit : (fun p => ∫ x, h (p, ψ x) * w x ∂ν)
      = fun p => (∫ x, (w x).re • h (p, ψ x) ∂ν) + ∫ x, (w x).im • h₂ (p, ψ x) ∂ν := by
    funext p
    rw [← integral_add (integrable_weight hu₁ hψ hK hψK hh.continuous p)
      (integrable_weight hu₂ hψ hK hψK hh₂.continuous p)]
    exact integral_congr_ae (Eventually.of_forall fun x => hdec _ _)
  refine ⟨?_, fun p v => ?_⟩
  · rw [hsplit]
    exact (contDiff_weight hu₁ hψ hK hψK hh).add (contDiff_weight hu₂ hψ hK hψK hh₂)
  · have hd : Differentiable ℝ h := hh.differentiable (by simp)
    have hD := (hasFDerivAt_weight hu₁ hψ hK hψK hh p).add
      (hasFDerivAt_weight hu₂ hψ hK hψK hh₂ p)
    have hfd := hD.fderiv
    have hi₁ := integrable_weight hu₁ hψ hK hψK (contDiff_pderiv hh).continuous p
    have hi₂ := integrable_weight hu₂ hψ hK hψK (contDiff_pderiv hh₂).continuous p
    have hp₂ : ∀ y, pderiv h₂ (p, y) v = Complex.I * pderiv h (p, y) v := by
      intro y
      have h1 : HasFDerivAt (fun q => h (q, y)) (pderiv h (p, y)) p :=
        ((hasFDerivAt_partial hd p y).differentiableAt).hasFDerivAt
      have h2 : HasFDerivAt (fun q => h₂ (q, y)) (Complex.I • pderiv h (p, y)) p := by
        exact h1.const_smul Complex.I
      have : pderiv h₂ (p, y) = Complex.I • pderiv h (p, y) := h2.fderiv
      rw [this]; simp
    rw [hsplit]
    change fderiv ℝ ((fun p => ∫ x, (w x).re • h (p, ψ x) ∂ν) +
      (fun p => ∫ x, (w x).im • h₂ (p, ψ x) ∂ν)) p v = _
    rw [hfd, ContinuousLinearMap.add_apply, ContinuousLinearMap.integral_apply hi₁,
      ContinuousLinearMap.integral_apply hi₂,
      ← integral_add (hi₁.apply_continuousLinearMap v) (hi₂.apply_continuousLinearMap v)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.smul_apply]
    rw [hp₂]
    exact (hdec _ _).symm

end GlobalTheory.CompanionTheory.SmoothParam
