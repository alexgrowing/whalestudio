import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.C.Sf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def locU (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) : UnitaryRep (Gw n w) (LL μ) :=
  (rightRegularRep (rationalGLOne K n) μ).compHom ((MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w))
    (MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1)

theorem locU_apply (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (g : Gw n w) : locU μ w g = rhoL μ w g := rfl

theorem fixU_locU (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w)) :
    fixU (locU μ w) J = fixL μ w J := by
  ext v
  simp only [mem_fixU, fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    exact h u hu
  · intro h u hu
    exact h _ (Subgroup.mem_map_of_mem _ hu)

end UpperTheory.ConvolutionTheory.C.Sf
