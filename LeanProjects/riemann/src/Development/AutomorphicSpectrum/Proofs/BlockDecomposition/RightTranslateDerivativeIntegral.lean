import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpIntegralAePointwiseStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.IntForm

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem Rd_continuousOn {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContinuousOn (Rd X f) (GLs n) :=
  (GlobalTheory.CompanionTheory.SobGL.Smooth.contDiffOn_fderiv_apply' (GlobalTheory.CompanionTheory.SobGL.Smooth.isOpen_GLs' n) hf
    (GlobalTheory.CompanionTheory.SobGL.Smooth.mulRight' X).contDiff.contDiffOn).continuousOn

theorem hasDerivAt_curve {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) (z : G n) (s : ℝ) :
    HasDerivAt (fun r : ℝ => f (z.val * (expC X r).val)) (Rd X f (z.val * (expC X s).val)) s := by
  have hγ := (GlobalTheory.T.matrix_exp_curve_derivative n X).2 s
  let L : CLof (Mat n) (Mat n) := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ z.val)
  have h1 : HasDerivAt (fun r : ℝ => z.val * (expC X r).val) (z.val * ((expC X s).val * X)) s :=
    L.hasFDerivAt.comp_hasDerivAt s hγ
  have hw : (z.val * (expC X s).val) ∈ GLs n := val_mem_GLs (z * expC X s)
  have h2 : HasFDerivAt f (fderiv ℝ f (z.val * (expC X s).val)) (z.val * (expC X s).val) :=
    ((hf.contDiffAt ((GlobalTheory.CompanionTheory.SobGL.Smooth.isOpen_GLs' n).mem_nhds hw)).differentiableAt
      (by simp)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt s h1
  have e : z.val * ((expC X s).val * X) = (z.val * (expC X s).val) * X := (Matrix.mul_assoc _ _ _).symm
  rw [e] at h3
  exact h3

theorem continuous_F {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    Continuous (fun p : ℝ × G n => Rd X f (p.2.val * (expC X p.1).val)) := by
  have hc : Continuous (fun p : ℝ × G n => p.2 * expC X p.1) :=
    continuous_snd.mul ((GlobalTheory.T.matrix_exp_curve_derivative n X).1.comp continuous_fst)
  have hv : Continuous (fun p : ℝ × G n => (p.2 * expC X p.1).val) := Units.continuous_val.comp hc
  exact (Rd_continuousOn hf X).comp_continuous hv (fun p => val_mem_GLs (p.2 * expC X p.1))

section L2

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem rR_cls_ae (hU : Unimod) {g : Mat n → V} (hg : MemLp (fun y : G n => g y.val) 2 μ) (h : G n) :
    rR μ V h (cls μ g) =ᵐ[μ] fun z => g (z.val * h.val) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have h1 := hm.quasiMeasurePreserving.ae_eq_comp (coe_cls μ hg)
  filter_upwards [rR_coe μ hU h (cls μ g), h1] with z hz1 hz2
  rw [hz1]
  simpa using hz2

theorem setIntegral_ae (hU : Unimod) {f : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hg : MemLp (fun y : G n => Rd X f y.val) 2 μ) (a b : ℝ) :
    (⇑(∫ s in Set.Ioc a b, rR μ V (expC X s) (cls μ (Rd X f))) : G n → V) =ᵐ[μ]
      fun z => ∫ s in Set.Ioc a b, Rd X f (z.val * (expC X s).val) := by
  have hc : Continuous (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f))) :=
    ((GlobalTheory.T.regular_representation_continuous n μ V hU (cls μ (Rd X f))).1).comp (GlobalTheory.T.matrix_exp_curve_derivative n X).1
  have hint : Integrable (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f)))
      (volume.restrict (Set.Ioc a b)) := hc.integrableOn_Ioc
  refine GlobalTheory.T.lp_integral_ae_pointwise ℝ (G n) V (volume.restrict (Set.Ioc a b)) μ _
    (fun s z => Rd X f (z.val * (expC X s).val)) hint ?_ ?_
  · have : Continuous (Function.uncurry fun (s : ℝ) (z : G n) => Rd X f (z.val * (expC X s).val)) :=
      continuous_F hf X
    exact this.aestronglyMeasurable
  · exact ae_of_all _ fun s => rR_cls_ae μ hU hg (expC X s)

end L2

theorem rR_sub_cls_eq_integral : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (f : Mat n → V) (X : Mat n), ContDiffOn ℝ ∞ f (GLs n) → MemLp (fun y : G n => f y.val) 2 μ → MemLp (fun y : G n => Rd X f y.val) 2 μ → ∀ t : ℝ, rR μ V (expC X t) (cls μ f) - cls μ f = ∫ s in (0 : ℝ)..t, rR μ V (expC X s) (cls μ (Rd X f)) := by
  intro n _ _ μ _ V _ _ _ hU f X hf hfm hg t
  apply Lp.ext
  rw [intervalIntegral]
  have hsub1 := Lp.coeFn_sub (rR μ V (expC X t) (cls μ f)) (cls μ f)
  have hsub2 := Lp.coeFn_sub (∫ s in Set.Ioc 0 t, rR μ V (expC X s) (cls μ (Rd X f)))
    (∫ s in Set.Ioc t 0, rR μ V (expC X s) (cls μ (Rd X f)))
  filter_upwards [hsub1, hsub2, rR_cls_ae μ hU hfm (expC X t), coe_cls μ hfm,
    setIntegral_ae μ hU X hf hg 0 t, setIntegral_ae μ hU X hf hg t 0] with z h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, h6]
  have hcont : Continuous (fun s : ℝ => Rd X f (z.val * (expC X s).val)) :=
    (continuous_F hf X).comp (Continuous.prodMk continuous_id continuous_const)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (f := fun r : ℝ => f (z.val * (expC X r).val))
    (f' := fun s : ℝ => Rd X f (z.val * (expC X s).val))
    (fun s _ => hasDerivAt_curve hf X z s) (hcont.intervalIntegrable _ _)
  rw [intervalIntegral] at key
  rw [key]
  simp [expC_zero]

end GlobalTheory.CompanionTheory.PresSobA.IntForm
