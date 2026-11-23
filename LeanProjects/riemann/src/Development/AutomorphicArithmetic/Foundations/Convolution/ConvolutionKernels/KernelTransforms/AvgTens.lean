import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.avgTens :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n) (Φ : AdelicGLn.AdelicGL K n → ℂ),
      (∀ g, Φ g = β (infPart K n g) * e (finPart K n g)) →
      (∀ x, PositivityTheory.Rg.Tf.Geo.avg Φ x = tens β e x) ∧
      ∀ g : AdelicGLn.AdelicGL K n, archEquiv K n (PositivityTheory.Rg.Tf.Geo.mapGL n (RingHom.fst _ _) g) = infPart K n g := by
  intro K _ _ n hn β e Φ hΦ
  refine ⟨fun x => ?_, fun g => ?_⟩
  · have hemb : MeasurableEmbedding GroundTheory.Global.expPos :=
      GroundTheory.Global.expPosHomeomorph.measurableEmbedding
    rw [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).1 x, tensFun, kbar, GroundTheory.Global.posRealMeasure_eq_map_expPos,
      hemb.integral_map, ← integral_mul_const]
    unfold PositivityTheory.Rg.Tf.Geo.avg
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have h1 : infPart K n (centralSection K n (GroundTheory.Global.expPos t) * (x : AdelicGLn.AdelicGL K n)) =
        infPart K n (x : AdelicGLn.AdelicGL K n) * zInf K n (GroundTheory.Global.expPos t) := by
      rw [map_mul (infPart K n), ← zInf_mul_comm]
      rfl
    have h2 : CuspidalSpectrum.finPart K n (centralSection K n (GroundTheory.Global.expPos t) * (x : AdelicGLn.AdelicGL K n)) =
        CuspidalSpectrum.finPart K n (x : AdelicGLn.AdelicGL K n) := by
      rw [map_mul (CuspidalSpectrum.finPart K n), finPart_centralSection, one_mul]
    change Φ (centralSection K n (GroundTheory.Global.expPos t) * (x : AdelicGLn.AdelicGL K n)) = _
    rw [hΦ, h1, h2]
  · rw [infPart_apply]
    rfl
