import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.WhittakerHecke.RealIdeleMulAbsContinuousAndUnitAbsEqOne
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem gen {T U P Y Q : Type*} [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace Y]
    [MeasurableSpace Q] [Countable Q] [MeasurableSingletonClass Q]
    (τ : Measure T) (υ : Measure U) (ν : Measure P) (μ : Measure Y) [SFinite τ] [SFinite υ] [SFinite ν] [SFinite μ]
    (f : T → U → P → Q → Y) (hf : Measurable fun x : T × U × P × Q => f x.1 x.2.1 x.2.2.1 x.2.2.2) (c : ℝ≥0)
    (hc : ∀ p, ∀ h : Y → ℝ≥0∞, Measurable h → ∫⁻ t, ∫⁻ u, ∑' α, h (f t u p α) ∂υ ∂τ = c * ∫⁻ y, h y ∂μ)
    (H : Y × P → ℂ) (hH : Measurable H) (hI : Integrable H (μ.prod ν)) :
    (∀ᵐ t ∂τ, ∀ᵐ u ∂υ, ∀ᵐ p ∂ν, Summable fun α => H (f t u p α, p)) ∧
      ∫ t, ∫ u, ∫ p, ∑' α, H (f t u p α, p) ∂ν ∂υ ∂τ = (c : ℂ) * ∫ q, H q ∂(μ.prod ν) := by
  let Ψ : T × U × P × Q → Y × P := fun x => (f x.1 x.2.1 x.2.2.1 x.2.2.2, x.2.2.1)
  have hΨ : Measurable Ψ := hf.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))
  let m : Measure (T × U × P × Q) := τ.prod (υ.prod (ν.prod Measure.count))
  have hmap : m.map Ψ = c • μ.prod ν := by
    refine Measure.ext_of_lintegral _ fun h hh => ?_
    have hΨh : Measurable fun x => h (Ψ x) := hh.comp hΨ
    have hG : Measurable fun x : T × U × P => ∑' α, h (f x.1 x.2.1 x.2.2 α, x.2.2) :=
      Measurable.ennreal_tsum fun α => hΨh.comp (f := fun x : T × U × P => (x.1, x.2.1, x.2.2, α)) (by fun_prop)
    rw [lintegral_map hh hΨ, lintegral_smul_measure, lintegral_prod _ hΨh.aemeasurable, lintegral_prod_symm _ hh.aemeasurable]
    have e1 : ∀ t, ∫⁻ y, h (Ψ (t, y)) ∂(υ.prod (ν.prod Measure.count)) =
        ∫⁻ p, ∫⁻ u, ∑' α, h (f t u p α, p) ∂υ ∂ν := by
      intro t
      have a1 : Measurable fun y : U × P × Q => h (Ψ (t, y)) := hΨh.comp measurable_prodMk_left
      have a2 : Measurable (Function.uncurry fun (u : U) (p : P) => ∑' α, h (f t u p α, p)) :=
        hG.comp (measurable_prodMk_left (x := t))
      rw [lintegral_prod _ a1.aemeasurable, ← lintegral_lintegral_swap a2.aemeasurable]
      refine lintegral_congr fun u => ?_
      have a3 : Measurable fun y : P × Q => h (Ψ (t, u, y)) := a1.comp measurable_prodMk_left
      rw [lintegral_prod _ a3.aemeasurable]
      refine lintegral_congr fun p => ?_
      rw [lintegral_count]
    simp only [e1]
    have hG2 : Measurable fun x : T × P => ∫⁻ u, ∑' α, h (f x.1 u x.2 α, x.2) ∂υ :=
      Measurable.lintegral_prod_right' (f := fun x : (T × P) × U => ∑' α, h (f x.1.1 x.2 x.1.2 α, x.1.2))
        (hG.comp (f := fun x : (T × P) × U => (x.1.1, x.2, x.1.2)) (by fun_prop))
    rw [lintegral_lintegral_swap hG2.aemeasurable]
    have e2 : ∀ p, ∫⁻ t, ∫⁻ u, ∑' α, h (f t u p α, p) ∂υ ∂τ = c * ∫⁻ y, h (y, p) ∂μ :=
      fun p => hc p (fun y => h (y, p)) (hh.comp measurable_prodMk_right)
    simp only [e2]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    rfl
  have hI1 : Integrable H (m.map Ψ) := by
    rw [hmap]
    exact hI.smul_measure ENNReal.coe_ne_top
  have hI2 : Integrable (fun x => H (Ψ x)) m := (integrable_map_measure hH.aestronglyMeasurable hΨ.aemeasurable).1 hI1
  have hval : ∫ x, H (Ψ x) ∂m = (c : ℂ) * ∫ q, H q ∂(μ.prod ν) := by
    rw [← integral_map hΨ.aemeasurable hH.aestronglyMeasurable, hmap, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]
  constructor
  · filter_upwards [hI2.prod_right_ae] with t ht
    filter_upwards [ht.prod_right_ae] with u hu
    filter_upwards [hu.prod_right_ae] with p hp
    exact (integrable_count_iff.1 hp).of_norm
  · rw [← hval, integral_prod _ hI2]
    refine integral_congr_ae ?_
    filter_upwards [hI2.prod_right_ae] with t ht
    rw [integral_prod _ ht]
    refine integral_congr_ae ?_
    filter_upwards [ht.prod_right_ae] with u hu
    rw [integral_prod _ hu]
    refine integral_congr_ae ?_
    filter_upwards [hu.prod_right_ae] with p hp
    rw [integral_countable hp]
    simp [Ψ]

theorem UpperTheory.integral_tsum_ideleCovering_eq_const_mul :
    ∀ (U : UMeas) (c : ℝ≥0), (∀ h : IdeleGroup ℚ → ℝ≥0∞, Measurable h →
          ∫⁻ t : ℝ, ∫⁻ u, ∑' α : ℚˣ, h (Un.cov t u α) ∂U.υ = c * ∫⁻ y, h y ∂(ideleMeasure ℚ)) →
        ∀ (κ : Measure (G1 ℚ)) [IsProbabilityMeasure κ] (H : IdeleGroup ℚ × IdeleGroup ℚ × G1 ℚ → ℂ), Measurable H →
        Integrable H ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod κ)) →
        (∀ᵐ t : ℝ, ∀ᵐ u ∂U.υ, ∀ᵐ p ∂((ideleMeasure ℚ).prod κ), Summable fun α : ℚˣ => H (Un.cov t u α * (p.1 * p.1)⁻¹, p)) ∧
        ∫ t : ℝ, ∫ u, ∫ p, ∑' α : ℚˣ, H (Un.cov t u α * (p.1 * p.1)⁻¹, p) ∂((ideleMeasure ℚ).prod κ) ∂U.υ =
          (c : ℂ) * ∫ q, H q ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod κ)) := by
  intro U c hc κ _ H hH hI
  haveI := U.prob
  letI : MeasurableSpace ℚˣ := ⊤
  haveI : MeasurableSingletonClass ℚˣ := ⟨fun _ => trivial⟩
  haveI : Countable ℚˣ := Units.val_injective.countable
  have hiy : Measurable (fun t : ℝ => (iy (Real.exp t) : IdeleGroup ℚ)) := by
    have h : Continuous (fun t : ℝ => (iy (Real.exp t) : IdeleGroup ℚ)) := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one.2.2.1
    exact h.measurable
  have hd : Measurable (fun α : ℚˣ => (IdeleGroup.diagonal ℚ α : IdeleGroup ℚ)) := measurable_from_top
  refine gen volume U.υ ((ideleMeasure ℚ).prod κ) (ideleMeasure ℚ)
    (fun t u p α => Un.cov t u α * (p.1 * p.1)⁻¹) ?_ c ?_ H hH hI
  · have h1 : Measurable fun x : ℝ × IdeleGroup ℚ × (IdeleGroup ℚ × G1 ℚ) × ℚˣ => x.2.2.1.1 := by fun_prop
    exact (((hd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).mul
      ((hiy.comp measurable_fst).mul (hiy.comp measurable_fst))).mul (measurable_fst.comp measurable_snd)).mul (h1.mul h1).inv
  · intro p h hh
    rw [hc (fun y => h (y * (p.1 * p.1)⁻¹)) (hh.comp (measurable_mul_const _)), lintegral_mul_right_eq_self]
