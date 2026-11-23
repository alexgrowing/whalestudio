import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfT :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfT F := by
  intro F _ _ f hf t g
  unfold Wf
  rw [← int_mul (h := fun x => f (gl (nU x) * (aE (IdeleGroup.diagonal F t) * g)) * ψ x)
    (fun k x => by rw [hf.per, ψ_add, ψ_rt, one_mul]) t]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  obtain ⟨γ, hγ⟩ := rat_a t
  have := a_n (IdeleGroup.diagonal F t) x
  simp only
  rw [← hf.2 γ (gl (nU x) * g), hγ, ← mul_assoc, ← mul_assoc, this]
  rfl
