import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.mkLaws :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), (∀ u t u' t', D.mkE u t * D.mkE u' t' = D.mkE (u * u' + rt D.δ * (t * t')) (u * t' + t * u')) ∧
      (∀ u t u' t', D.mkE u t + D.mkE u' t' = D.mkE (u + u') (t + t')) ∧ D.mkE 1 0 = 1 ∧ (∀ u t, D.co (D.mkE u t) = ![u, t]) ∧
      (∀ z, D.mkE (D.co z 0) (D.co z 1) = z) ∧ (∀ u t, D.bar (D.mkE u t) = D.mkE u (-t)) ∧
      ∀ (z : (A E)ˣ) u t, (z : A E) = D.mkE u t → ((ideleNorm F E z : (A F)ˣ) : A F) = u ^ 2 - rt D.δ * t ^ 2 := by
  intro F E _ _ _ _ _ D
  refine ⟨D.mkE_mul, fun u t u' t' => (D.mkE_add u t u' t').symm, D.mkE_one, D.co_mkE, D.mkE_co, D.bar_mkE, ?_⟩
  intro z u t h
  have hc := D.co_mkE u t
  rw [D.coe_ideleNorm, h, hc]
  simp
