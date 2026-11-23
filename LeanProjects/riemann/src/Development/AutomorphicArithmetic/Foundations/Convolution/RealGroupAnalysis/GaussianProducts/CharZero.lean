import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RealDiff

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private lemma bdd_int {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (u g : Ω → ℂ)
    (hu : Measurable u) (hb : ∀ ω, ‖u ω‖ ≤ 1) (hg : Integrable g ν) :
    Integrable (fun ω => u ω * g ω) ν := by
  refine Integrable.mono' hg.norm (hu.aestronglyMeasurable.mul hg.1) (ae_of_all _ fun ω => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb ω)

private lemma real_diff {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hGb : ∀ x, ‖G x‖ ≤ 1) :
    ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X)
      - ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X)
      = ∫ ω, G (X ω) * (f ω : ℂ) ∂ν :=
  _root_.UpperTheory.Reformulated.B.Qh3.real_diff ν X f hX hf G hG hGb

private lemma real_case {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (h : ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (f ω : ℂ) ∂ν = 0)
    (S : Set (ι → ℝ)) (hS : MeasurableSet S) :
    ∫ ω, S.indicator 1 (X ω) * (f ω : ℂ) ∂ν = 0 := by
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (-f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hEq : (ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X
      = (ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X := by
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    rw [charFunDual_apply, charFunDual_apply]
    have key := real_diff ν X f hX hf (fun x => Complex.exp ((L x : ℂ) * Complex.I))
      (by fun_prop) (fun x => by rw [Complex.norm_exp_ofReal_mul_I])
    have h0 := h (fun i => L (fun j => if i = j then 1 else 0))
    have hL : ∀ x : ι → ℝ, L x = ∑ i, L (fun j => if i = j then 1 else 0) * x i := by
      intro x
      have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
      simpa [mul_comm] using this
    simp only [← hL] at h0
    rw [h0] at key
    exact sub_eq_zero.mp key
  have key := real_diff ν X f hX hf (S.indicator 1)
    (measurable_one.indicator hS) (fun x => by
      by_cases hx : x ∈ S <;> simp [hx])
  rw [hEq, sub_self] at key
  exact key.symm

theorem UpperTheory.ConvolutionTheory.R2.G.charZero :
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (X : Ω → ι → ℝ) (ρ : Ω → ℂ), Measurable X → Integrable ρ ν →
    (∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω ∂ν = 0) →
    ∀ S : Set (ι → ℝ), MeasurableSet S → ∫ ω, S.indicator 1 (X ω) * ρ ω ∂ν = 0 := by
  intro Ω ι _ _ ν X ρ hX hρ h S hS
  have hconjI : Integrable (fun ω => (starRingEnd ℂ) (ρ ω)) ν := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hρ
  have hE : ∀ t : ι → ℝ, Measurable fun ω =>
      Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) := by
    intro t
    have : ∀ i, Measurable fun ω => X ω i := fun i => (measurable_pi_apply i).comp hX
    fun_prop
  have hEb : ∀ (t : ι → ℝ) (ω : Ω),
      ‖Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro t ω
    rw [Complex.norm_exp_ofReal_mul_I]
  have hc : ∀ t : ι → ℝ,
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω) ∂ν = 0 := by
    intro t
    have h1 := congrArg (starRingEnd ℂ) (h (-t))
    rw [← integral_conj, map_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
    simp
  have hlin : ∀ (a b : ℂ) (t : ι → ℝ),
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω)) ∂ν = 0 := by
    intro a b t
    have e1 := bdd_int ν _ ρ (hE t) (hEb t) hρ
    have e2 := bdd_int ν _ _ (hE t) (hEb t) hconjI
    have : ∀ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω))
        = a * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω)
          + b * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω)) := by
      intro ω; ring
    simp only [this]
    rw [integral_add (e1.const_mul a) (e2.const_mul b), integral_const_mul, integral_const_mul,
      h t, hc t]
    simp
  have hre : Integrable (fun ω => (ρ ω).re) ν := hρ.re
  have him : Integrable (fun ω => (ρ ω).im) ν := hρ.im
  have r1 := real_case ν X (fun ω => (ρ ω).re) hX hre (fun t => by
    rw [← hlin (1 / 2) (1 / 2) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).re : ℂ) = 1 / 2 * ρ ω + 1 / 2 * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.re_eq_add_conj]; ring
    simp only [this]) S hS
  have r2 := real_case ν X (fun ω => (ρ ω).im) hX him (fun t => by
    rw [← hlin (1 / (2 * Complex.I)) (-(1 / (2 * Complex.I))) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).im : ℂ) = 1 / (2 * Complex.I) * ρ ω
        + -(1 / (2 * Complex.I)) * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.im_eq_sub_conj]; ring
    simp only [this]) S hS
  have hind : Measurable fun ω => S.indicator (1 : (ι → ℝ) → ℂ) (X ω) :=
    (measurable_one.indicator hS).comp hX
  have hindb : ∀ ω, ‖S.indicator (1 : (ι → ℝ) → ℂ) (X ω)‖ ≤ 1 := by
    intro ω
    by_cases hx : X ω ∈ S <;> simp [hx]
  have i1 := bdd_int ν _ (fun ω => ((ρ ω).re : ℂ)) hind hindb hre.ofReal
  have i2 := bdd_int ν _ (fun ω => ((ρ ω).im : ℂ)) hind hindb him.ofReal
  have hsplit : ∀ ω, S.indicator 1 (X ω) * ρ ω
      = S.indicator 1 (X ω) * ((ρ ω).re : ℂ)
        + Complex.I * (S.indicator 1 (X ω) * ((ρ ω).im : ℂ)) := by
    intro ω
    conv_lhs => rw [← Complex.re_add_im (ρ ω)]
    ring
  simp only [hsplit]
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, r1, r2]
  simp
