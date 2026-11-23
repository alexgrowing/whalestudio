import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.C.olocEx :
    UpperTheory.ConvolutionTheory.C.OlocEx := by
  intro K _ _ n μ _ w _ _ m _ φ hφ
  have hL : MemLp φ 1 m := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  let π : UnitaryRep (Gw n w) (LL μ) := (rightRegularRep (rationalGLOne K n) μ).compHom
    ((MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w))
    (MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1)
  refine ⟨π.integrated m hL.toLp, fun u v => ?_, fun T hT => ?_⟩
  · have hπ : ∀ g, π g v = rhoL μ w g v := fun _ => rfl
    rw [UnitaryRep.inner_integrated]
    refine integral_congr_ae ((MemLp.coeFn_toLp hL).mono fun g hg => ?_)
    simp only [hπ]
    rw [hg]
  · refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
    rw [hT u v, UnitaryRep.inner_integrated]
    have hπ : ∀ g, π g v = rhoL μ w g v := fun _ => rfl
    refine integral_congr_ae ((MemLp.coeFn_toLp hL).mono fun g hg => ?_)
    simp only [hπ]
    rw [hg]
