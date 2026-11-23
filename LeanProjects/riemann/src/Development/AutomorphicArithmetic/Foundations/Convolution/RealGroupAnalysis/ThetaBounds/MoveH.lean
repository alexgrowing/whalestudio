import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Mov
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OpsFock

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.moveH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), MoveH O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ w h
  obtain ⟨G, c, hP, hG, hD⟩ := curveH F E D O W w
  have hF := opsFock F E D O
  have hh : O.h w φ ∈ Fock D.δ := by
    have h2 : O.h w φ = (∑ i, O.x w i (O.d w i φ)) + (2 : ℂ) • φ := by
      simp [Fo.Ops.h, LinearMap.sum_apply, two_smul, LinearMap.add_apply, Module.End.mul_apply, one_add_one_eq_two.symm, add_mul, Module.End.one_apply]
      rw [add_smul, one_smul]
    rw [h2]
    exact add_mem (sum_mem fun i _ => (hF w i _ (hF w i φ hφ).2).1) (Submodule.smul_mem _ _ hφ)
  have hm := congrFun (mov F E D W M π f hf φ hφ (O.h w φ) hh G c _ hP hG (hD φ)) h
  rw [hm, map_sub, LinearMap.sub_apply]
  rfl
