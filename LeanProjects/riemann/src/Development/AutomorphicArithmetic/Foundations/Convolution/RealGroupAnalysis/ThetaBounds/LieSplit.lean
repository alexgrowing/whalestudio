import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieSplit {E : Type} [Field E] [NumberField E] (X : Lie E 2) :
    ∃ (Y : Lie E 2) (s : Cinf E), (Matrix.of Y).trace = 0 ∧ X = Y + zE s ∧ X 0 0 + X 1 1 = s + s := by
  have h : X 0 0 + X 1 1 = (2⁻¹ : ℝ) • (X 0 0 + X 1 1) + (2⁻¹ : ℝ) • (X 0 0 + X 1 1) := by
    rw [← add_smul]; norm_num
  refine ⟨X - zE ((2⁻¹ : ℝ) • (X 0 0 + X 1 1)), _, ?_, (sub_add_cancel _ _).symm, h⟩
  rw [Matrix.trace_fin_two]
  change (X 0 0 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) + (X 1 1 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) = 0
  linear_combination h
