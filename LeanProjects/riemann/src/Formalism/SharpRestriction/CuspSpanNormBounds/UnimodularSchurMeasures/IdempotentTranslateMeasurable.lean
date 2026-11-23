import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Grp

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin (2 * r + k + 1) → Bool}
  {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}

theorem discrete_series_isometry (hσ : IsDSHpk k r ε lam σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (v : H) :
    ‖σ a v‖ = ‖v‖ := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have := hDS.2.2.1.2.1 _ (cayley_conj_mem_diagonal_model hP ha).1 v
  simpa only [(cayley_conj_mem_diagonal_model hP ha).2] using this

theorem discrete_series_inner (hσ : IsDSHpk k r ε lam σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (x y : H) :
    ⟪σ a x, σ a y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ a : H →ₗ[ℂ] H) (discrete_series_isometry hσ ha)).inner_map_map x y

theorem discrete_series_continuousOn (hσ : IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have h1 := hDS.2.2.1.2.2 v
  have hc : Continuous fun x : Mat k r => P * x * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h2 := h1.comp hc.continuousOn (fun a ha => (cayley_conj_mem_diagonal_model hP ha).1)
  refine h2.congr fun a ha => ?_
  simp only [Function.comp, (cayley_conj_mem_diagonal_model hP ha).2]

theorem isClosed_unitary_group (k r : ℕ) : IsClosed (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  have hc : Continuous fun g : Mat k r => gᴴ * Formalism.QuantumDeterminants.Hpk k r * g :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const

end Grp

namespace BData

variable (X : BData)

def EFix : Prop :=
  ∀ y : X.H, ∫ x, X.e (Matrix.of x) * ⟪y, X.σ (Matrix.of x) X.w⟫_ℂ ∂X.μG = ⟪y, X.w⟫_ℂ

def E2 (g y : Mat X.k X.r) : ℂ := (fdegH X.μG X.σ X.w : ℂ) * star ⟪X.σ g X.w, X.σ y X.w⟫_ℂ

variable {X}

theorem idempotent_translate_left (hX : X.Hyp) {g y : Mat X.k X.r} (hg : g ∈ X.G) (hy : y ∈ X.G) : X.E2 g (g * y) = X.e y := by
  show (fdegH X.μG X.σ X.w : ℂ) * star ⟪X.σ g X.w, X.σ (g * y) X.w⟫_ℂ =
    (fdegH X.μG X.σ X.w : ℂ) * star ⟪X.w, X.σ y X.w⟫_ℂ
  rw [discrete_series_map_mul hX.2.1 hg hy, ContinuousLinearMap.comp_apply, discrete_series_inner hX.2.1 hg]

theorem meas_orbit (hX : X.Hyp) (v : X.H) : AEStronglyMeasurable (fun y => X.σ (Matrix.of y) v) X.μG := by
  have hc : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt X.k X.r => X.σ (Matrix.of y) v) {y | Matrix.of y ∈ X.G} :=
    discrete_series_continuousOn hX.2.1 v
  have hm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt X.k X.r | Matrix.of y ∈ X.G} :=
    (show IsClosed {y : Formalism.QuantumDeterminants.Mt X.k X.r | Matrix.of y ∈ X.G} from isClosed_unitary_group X.k X.r).measurableSet
  have := hc.aestronglyMeasurable (μ := X.μG) hm
  have hae : ∀ᵐ y ∂X.μG, y ∈ {y : Formalism.QuantumDeterminants.Mt X.k X.r | Matrix.of y ∈ X.G} := ae_mem hX
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at this

theorem meas_Φ (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ) {x : Mat X.k X.r} (hx : x ∈ X.G) :
    AEStronglyMeasurable (fun y => X.Φ B χ (x * Matrix.of y)) X.μG :=
  hχ.2.2.1.comp_measurePreserving (mp_left hX hx)

theorem idempotent_translate_measurable (hX : X.Hyp) (g : Mat X.k X.r) : AEStronglyMeasurable (fun y => X.E2 g (Matrix.of y)) X.μG := by
  unfold E2
  refine AEStronglyMeasurable.const_mul ?_ _
  exact Complex.continuous_conj.comp_aestronglyMeasurable (aestronglyMeasurable_const.inner (meas_orbit hX X.w))

theorem subst (hX : X.Hyp) (B : X.H → X.Vp) (χ : Mat X.k X.r → ℝ) (x : Mat X.k X.r) {g : Mat X.k X.r}
    (hg : g ∈ X.G) :
    (fun y => X.E2 g (Matrix.of (Formalism.QuantumDeterminants.lmulM g y)) • X.Φ B χ (x * Matrix.of (Formalism.QuantumDeterminants.lmulM g y))) =ᵐ[X.μG]
      fun y => X.e (Matrix.of y) • X.Φ B χ (x * g * Matrix.of y) := by
  filter_upwards [ae_mem hX] with y hy
  have e1 : Matrix.of (Formalism.QuantumDeterminants.lmulM g y) = g * Matrix.of y := rfl
  rw [e1, idempotent_translate_left hX hg hy, Matrix.mul_assoc]

theorem meas_F (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ) {x : Mat X.k X.r}
    (hx : x ∈ X.G) (g : Mat X.k X.r) :
    AEStronglyMeasurable (fun y => X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)) X.μG :=
  (idempotent_translate_measurable hX g).smul (meas_Φ hX hχ hx)

theorem integrable_F (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ) (he : X.ConvolutionKernelIntegrable)
    {x g : Mat X.k X.r} (hx : x ∈ X.G) (hg : g ∈ X.G) :
    Integrable (fun y => X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)) X.μG := by
  have h1 : Integrable (fun y => X.e (Matrix.of y) • X.Φ B χ (x * g * Matrix.of y)) X.μG :=
    integrable_conv hX hχ he (unitary_group_mul_mem hx hg)
  have h2 := h1.congr (subst hX B χ x hg).symm
  exact ((mp_left hX hg).integrable_comp (meas_F hX hχ hx g)).1 h2

theorem integral_F (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ)
    {x g : Mat X.k X.r} (hx : x ∈ X.G) (hg : g ∈ X.G) :
    ∫ y, X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y) ∂X.μG =
      ∫ y, X.e (Matrix.of y) • X.Φ B χ (x * g * Matrix.of y) ∂X.μG := by
  rw [← integral_congr_ae (subst hX B χ x hg)]
  have hmp := mp_left hX hg
  have hm : AEStronglyMeasurable (fun y => X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y))
      (X.μG.map (Formalism.QuantumDeterminants.lmulM g)) := by rw [hmp.map_eq]; exact meas_F hX hχ hx g
  have := integral_map hmp.measurable.aemeasurable hm
  rw [hmp.map_eq] at this
  exact this

theorem integral_normF (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ)
    {x g : Mat X.k X.r} (hx : x ∈ X.G) (hg : g ∈ X.G) :
    ∫ y, ‖X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)‖ ∂X.μG =
      ∫ y, ‖X.e (Matrix.of y) • X.Φ B χ (x * g * Matrix.of y)‖ ∂X.μG := by
  rw [← integral_congr_ae ((subst hX B χ x hg).mono fun y hy => congrArg norm hy)]
  have hmp := mp_left hX hg
  have hm : AEStronglyMeasurable (fun y => ‖X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)‖)
      (X.μG.map (Formalism.QuantumDeterminants.lmulM g)) := by rw [hmp.map_eq]; exact (meas_F hX hχ hx g).norm
  have := integral_map hmp.measurable.aemeasurable hm
  rw [hmp.map_eq] at this
  exact this

theorem idempotent_convolution_self (hf : X.EFix) (y : Mat X.k X.r) :
    ∫ g, X.e (Matrix.of g) * X.E2 (Matrix.of g) y ∂X.μG = X.e y := by
  have h1 : ∀ g : Formalism.QuantumDeterminants.Mt X.k X.r, X.e (Matrix.of g) * X.E2 (Matrix.of g) y =
      (fdegH X.μG X.σ X.w : ℂ) * (X.e (Matrix.of g) * ⟪X.σ y X.w, X.σ (Matrix.of g) X.w⟫_ℂ) := by
    intro g
    unfold E2
    rw [show star ⟪X.σ (Matrix.of g) X.w, X.σ y X.w⟫_ℂ = ⟪X.σ y X.w, X.σ (Matrix.of g) X.w⟫_ℂ from
      inner_conj_symm _ _]
    ring
  simp only [h1]
  rw [integral_const_mul, hf (X.σ y X.w)]
  show (fdegH X.μG X.σ X.w : ℂ) * ⟪X.σ y X.w, X.w⟫_ℂ = (fdegH X.μG X.σ X.w : ℂ) * star ⟪X.w, X.σ y X.w⟫_ℂ
  rw [show star ⟪X.w, X.σ y X.w⟫_ℂ = ⟪X.σ y X.w, X.w⟫_ℂ from inner_conj_symm _ _]

theorem idem_of (hX : X.Hyp) {B : X.H → X.Vp} (he : X.ConvolutionKernelIntegrable) (hf : X.EFix) : X.IdemStep B := by
  intro χ hχ x hx
  have : SigmaFinite X.μG := hX.2.2.2.2.1.1
  obtain ⟨M, hM⟩ := hχ.2.2.2.1
  set f : Formalism.QuantumDeterminants.Mt X.k X.r → Formalism.QuantumDeterminants.Mt X.k X.r → X.Vp := fun g y =>
    (X.e (Matrix.of g) * X.E2 (Matrix.of g) (Matrix.of y)) • X.Φ B χ (x * Matrix.of y) with hfdef

  have hmeas : AEStronglyMeasurable (Function.uncurry f) (X.μG.prod X.μG) := by
    have m1 : AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r => X.e (Matrix.of p.1))
        (X.μG.prod X.μG) := he.aestronglyMeasurable.comp_fst
    have m2 : AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r =>
        X.E2 (Matrix.of p.1) (Matrix.of p.2)) (X.μG.prod X.μG) := by
      unfold E2
      refine AEStronglyMeasurable.const_mul ?_ _
      exact Complex.continuous_conj.comp_aestronglyMeasurable
        ((meas_orbit hX X.w).comp_fst.inner (meas_orbit hX X.w).comp_snd)
    have m3 : AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r =>
        X.Φ B χ (x * Matrix.of p.2)) (X.μG.prod X.μG) := (meas_Φ hX hχ hx).comp_snd
    exact (m1.mul m2).smul m3
  have hbound : ∀ g : Mat X.k X.r, g ∈ X.G →
      ∫ y, ‖X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)‖ ∂X.μG ≤ M * ∫ y, ‖X.e (Matrix.of y)‖ ∂X.μG := by
    intro g hg
    rw [integral_normF hX hχ hx hg, ← integral_const_mul]
    refine integral_mono_ae (integrable_conv hX hχ he (unitary_group_mul_mem hx hg)).norm (he.norm.const_mul M) ?_
    filter_upwards [ae_mem hX] with y hy
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _ (unitary_group_mul_mem (unitary_group_mul_mem hx hg) hy)) (norm_nonneg _)
  have hint : Integrable (Function.uncurry f) (X.μG.prod X.μG) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · filter_upwards [ae_mem hX] with g hg
      have := (integrable_F hX hχ he hx hg).smul (X.e (Matrix.of g))
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [Function.uncurry, hfdef, Pi.smul_apply, smul_smul]
    · refine Integrable.mono' (he.norm.mul_const (M * ∫ y, ‖X.e (Matrix.of y)‖ ∂X.μG))
        hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_mem hX] with g hg
      have e1 : ∀ y, ‖Function.uncurry f (g, y)‖ =
          ‖X.e (Matrix.of g)‖ * ‖X.E2 (Matrix.of g) (Matrix.of y) • X.Φ B χ (x * Matrix.of y)‖ := by
        intro y
        simp only [Function.uncurry, hfdef, mul_smul, norm_smul]
      simp only [e1]
      rw [integral_const_mul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (integral_nonneg fun y => norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hbound _ hg) (norm_nonneg _)

  have s1 : rconv X.μG X.e (X.Wf B χ) x = ∫ g, ∫ y, f g y ∂X.μG ∂X.μG := by
    unfold rconv
    refine integral_congr_ae ?_
    filter_upwards [ae_mem hX] with g hg
    have : X.Wf B χ (x * Matrix.of g) = ∫ y, X.E2 (Matrix.of g) (Matrix.of y) • X.Φ B χ (x * Matrix.of y) ∂X.μG := by
      rw [integral_F hX hχ hx hg]
      rfl
    rw [this, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hfdef, mul_smul]
  rw [s1, integral_integral_swap hint]
  unfold Wf rconv
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hfdef]
  rw [integral_smul_const, idempotent_convolution_self hf]

end BData

end Formalism.MainNotions.LeviCoordinates

end
