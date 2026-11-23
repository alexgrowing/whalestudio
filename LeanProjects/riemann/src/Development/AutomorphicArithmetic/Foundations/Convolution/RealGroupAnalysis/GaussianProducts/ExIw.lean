import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfNe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.exIw :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (π : TR.CuspSub F 2), ∃ f ∈ π.V, ∃ a, ∃ k ∈ KK F, Wf f.1 (gl (mD a * k)) ≠ 0 := by
  intro F _ _ _ _ π
  obtain ⟨f, hf, g, -, hg⟩ := UpperTheory.ConvolutionTheory.R2.Pp.wfNe F π
  obtain ⟨b, a, k, hk, rfl⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa F g
  refine ⟨f, hf, a, k, hk, fun h => hg ?_⟩
  have e : gl (nU b * mD a * k) = gl (nU b) * gl (mD a * k) := by
    rw [mul_assoc]
    exact map_mul _ _ _
  rw [e, ((UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1).2.1 b _), h, mul_zero]
