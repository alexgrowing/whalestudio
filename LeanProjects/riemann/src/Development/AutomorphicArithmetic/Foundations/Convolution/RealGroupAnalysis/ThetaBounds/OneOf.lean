import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormInf

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.oneOf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (_D : Dat F E), OneOf F E := by
  intro F E _ _ _ _ _ _ _ D y hy
  obtain ⟨u, hu, hn⟩ := normInf F E D (Matrix.GeneralLinearGroup.det y)
  have hu1 : u = 1 := by
    refine Units.ext (funext fun v => ?_)
    rw [hu v]
    have h1 : ∀ w : InfinitePlace E, ‖(Matrix.GeneralLinearGroup.det y).val w‖ = 1 := hy
    change _ = (1 : ℝ)
    refine Finset.prod_eq_one fun w _ => ?_
    split_ifs
    · rw [h1 w, one_pow]
    · rfl
  change ideleNorm F E (Matrix.GeneralLinearGroup.det (infGL E 2 y)) = 1
  rw [det_infGL, hn, hu1, map_one]
