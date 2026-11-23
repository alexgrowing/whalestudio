import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), LCen W := by
  intro F E _ _ _ _ _ _ _ D W z
  refine ⟨LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_), nu_scalar z⟩
  have hη : W.η.1 (ideleNorm F E z)⁻¹ = 1 := by rw [map_inv, W.η_norm, inv_one]
  have hs : (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ :=
    (map_inv _ _).symm
  have hv : D.act (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ v =
      fun i => (((ideleNorm F E z)⁻¹ : (A F)ˣ) : A F) * v i := by
    rw [hs, D.act_scalar, map_inv]; rfl
  rw [W.L_apply, W.Om_m, nu_scalar, hv, hη, ab_inv, ab_pow]
  simp
