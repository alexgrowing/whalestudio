import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Hermite1Integrable
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SplitA

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private noncomputable def hJ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (InfinitePlace F → ℝ) ≃ₜ InfiniteAdeleRing F where
  toEquiv := (TR.infEq F).toEquiv
  continuous_toFun := TR.continuous_infEq F
  continuous_invFun := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private lemma map_hJ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ c : NNReal, (infiniteAdeleMeasure F).map (hJ F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := by
  have hH : ((infiniteAdeleMeasure F).map (hJ F).symm).IsAddHaarMeasure :=
    (TR.infEq F).symm.toAddEquiv.isAddHaarMeasure_map (infiniteAdeleMeasure F)
      (hJ F).symm.continuous (hJ F).continuous
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul ((infiniteAdeleMeasure F).map (hJ F).symm)
    (volume : Measure (InfinitePlace F → ℝ))⟩

private lemma split_int {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {c : NNReal}
    (hc : (infiniteAdeleMeasure F).map (hJ F).symm = c • (volume : Measure (InfinitePlace F → ℝ)))
    (f : InfinitePlace F → ℝ → ℂ) (hf : ∀ w, Integrable (f w))
    (G : FiniteAdeleRing (𝓞 F) F → ℂ) :
    (Integrable G (finiteAdeleMeasure F) →
      Integrable (fun s : A F => (∏ w, f w (TR.pInf F s w)) * G s.2) (adeleMeasure F)) ∧
    ∫ s : A F, (∏ w, f w (TR.pInf F s w)) * G s.2 ∂(adeleMeasure F) =
      (c : ℂ) * (∏ w, ∫ t, f w t) * ∫ a, G a ∂(finiteAdeleMeasure F) := by
  have emb := (hJ F).symm.measurableEmbedding
  have hv : Integrable (fun y : InfinitePlace F → ℝ => ∏ w, f w (y w)) volume :=
    Integrable.fintype_prod hf
  have hv' : Integrable (fun y : InfinitePlace F → ℝ => ∏ w, f w (y w))
      ((infiniteAdeleMeasure F).map (hJ F).symm) := by
    rw [hc]
    exact hv.smul_measure ENNReal.coe_ne_top
  have hi : Integrable (fun z : InfiniteAdeleRing F => ∏ w, f w ((hJ F).symm z w))
      (infiniteAdeleMeasure F) := (emb.integrable_map_iff.1 hv')
  have hint : ∫ z : InfiniteAdeleRing F, ∏ w, f w ((hJ F).symm z w) ∂(infiniteAdeleMeasure F) =
      (c : ℂ) * ∏ w, ∫ t, f w t := by
    have h1 := emb.integral_map (μ := infiniteAdeleMeasure F)
      (fun y : InfinitePlace F → ℝ => ∏ w, f w (y w))
    rw [← h1, hc, integral_smul_nnreal_measure, volume_pi, integral_fintype_prod_eq_prod]
    rw [NNReal.smul_def, Complex.real_smul]
  refine ⟨fun hG => hi.mul_prod hG, ?_⟩
  have h2 := integral_prod_mul (μ := infiniteAdeleMeasure F) (ν := finiteAdeleMeasure F)
    (fun z : InfiniteAdeleRing F => ∏ w, f w ((hJ F).symm z w)) G
  rw [hint] at h2
  exact h2

private lemma gauss_prod {ι : Type} [Fintype ι] (y : ι → ℝ) :
    Complex.exp (-(Real.pi : ℂ) * ((∑ w, y w ^ 2 : ℝ) : ℂ)) =
      ∏ w, Complex.exp (-(Real.pi : ℂ) * (y w : ℂ) ^ 2) := by
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

private lemma eval_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (Q : Polynomial ℂ)
    (w : InfinitePlace F) :
    (fun v : V4 F => Q.eval ((TR.pInf F (v 1) w : ℝ) : ℂ)) ∈ polyFn (F := F) := by
  have h0 : (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ∈ polyFn (F := F) :=
    Algebra.subset_adjoin ⟨1, w, rfl⟩
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    have := (polyFn (F := F)).add_mem hp hq
    convert this using 1
    ext v
    simp [Polynomial.eval_add]
  | monomial n a =>
    have := (polyFn (F := F)).mul_mem ((polyFn (F := F)).algebraMap_mem a)
      ((polyFn (F := F)).pow_mem h0 n)
    convert this using 1
    ext v
    simp [Polynomial.eval_monomial]

theorem UpperTheory.ConvolutionTheory.R2.G.hermAdel :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : InfinitePlace F → ℕ), ∃ P : A F → ℂ, (fun v : V4 F => P (v 1)) ∈ polyFn (F := F) ∧
    ∀ g : FiniteAdeleRing (𝓞 F) F → ℂ, Integrable g (finiteAdeleMeasure F) →
    Integrable (fun s : A F => (∏ w, ((TR.pInf F s w : ℝ) : ℂ) ^ e w) * Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F s w ^ 2 : ℝ) : ℂ)) * g s.2) (adeleMeasure F) ∧
    ∀ x : A F, ∫ s : A F, (∏ w, ((TR.pInf F s w : ℝ) : ℂ) ^ e w) * Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F s w ^ 2 : ℝ) : ℂ)) * g s.2 * ψ (-(s * x)) ∂(adeleMeasure F) =
    P x * Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F x w ^ 2 : ℝ) : ℂ)) *
    ∫ s, g s * ((finiteAdelicChar F (-(s * x.2)) : Circle) : ℂ) ∂(finiteAdeleMeasure F) := by
  intro F _ _ _ e
  obtain ⟨c, hc⟩ := map_hJ F
  have hP := fun n => (hermite1 n).2
  choose Q hQ using hP
  have hH : ∀ y : InfinitePlace F → ℝ, (∏ w, ((y w : ℝ) : ℂ) ^ e w) *
      Complex.exp (-(Real.pi : ℂ) * ((∑ w, y w ^ 2 : ℝ) : ℂ)) =
      ∏ w, ((y w : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * (y w : ℂ) ^ 2)) := by
    intro y
    rw [gauss_prod, Finset.prod_mul_distrib]
  refine ⟨fun x => (c : ℂ) * ∏ w, (Q (e w)).eval ((TR.pInf F x w : ℝ) : ℂ), ?_, fun g hg => ⟨?_, fun x => ?_⟩⟩
  · have h1 : (fun v : V4 F => (∏ w, (Q (e w)).eval ((TR.pInf F (v 1) w : ℝ) : ℂ))) ∈ polyFn (F := F) := by
      have := (polyFn (F := F)).prod_mem (t := Finset.univ)
        (f := fun w => fun v : V4 F => (Q (e w)).eval ((TR.pInf F (v 1) w : ℝ) : ℂ))
        (fun w _ => eval_mem _ w)
      convert this using 1
      ext v
      simp [Finset.prod_apply]
    have := (polyFn (F := F)).mul_mem ((polyFn (F := F)).algebraMap_mem (c : ℂ)) h1
    convert this using 1
    ext v
    simp
  · have h := (split_int hc (fun w t => (t : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2))
      (fun w => (hermite1 (e w)).1) g).1 hg
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [hH]
  · have hS := (UpperTheory.ConvolutionTheory.R2.C.splitA F).2
    have hint : ∀ w : InfinitePlace F, Integrable (fun t : ℝ => (t : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (t * (TR.pInf F x w : ℝ)))) := by
      intro w
      refine (hermite1 (e w)).1.mono (Continuous.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall fun s => ?_)
      rw [norm_mul]
      have : ‖Complex.exp (2 * Real.pi * Complex.I * (s * (TR.pInf F x w : ℝ)))‖ = 1 := by
        have e1 : (2 * Real.pi * Complex.I * (s * (TR.pInf F x w : ℝ)) : ℂ) =
            ((2 * Real.pi * (s * TR.pInf F x w) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [e1, Complex.norm_exp_ofReal_mul_I]
      rw [this, mul_one]
    have h := (split_int hc (fun w t => (t : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (t * (TR.pInf F x w : ℝ)))) hint
      (fun a => g a * ((finiteAdelicChar F (-(a * x.2)) : Circle) : ℂ))).2
    have hcongr : ∀ s : A F, (∏ w, ((TR.pInf F s w : ℝ) : ℂ) ^ e w) * Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F s w ^ 2 : ℝ) : ℂ)) * g s.2 * ψ (-(s * x)) =
        (∏ w, (((TR.pInf F s w : ℝ) : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * ((TR.pInf F s w : ℝ) : ℂ) ^ 2) *
          Complex.exp (2 * Real.pi * Complex.I * (((TR.pInf F s w : ℝ) : ℂ) * (TR.pInf F x w : ℝ))))) *
        (g s.2 * ((finiteAdelicChar F (-(s.2 * x.2)) : Circle) : ℂ)) := by
      intro s
      have e1 : (-(s * x)).2 = -(s.2 * x.2) := rfl
      have e2 : ∀ w, TR.pInf F (-(s * x)) w = -(TR.pInf F s w * TR.pInf F x w) := by
        intro w
        rw [map_neg, map_mul]
        rfl
      rw [hS (-(s * x)), e1, hH, Finset.prod_mul_distrib (f := fun w => _ * _)]
      have e3 : ∀ w, Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F (-(s * x)) w : ℝ) : ℂ)) =
          Complex.exp (2 * Real.pi * Complex.I * (((TR.pInf F s w : ℝ) : ℂ) * (TR.pInf F x w : ℝ))) := by
        intro w
        rw [e2]
        congr 1
        push_cast
        ring
      simp only [e3]
      ring
    simp only [hcongr]
    rw [h]
    simp only [hQ]
    rw [Finset.prod_mul_distrib, gauss_prod]
    ring
