import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfT

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.AutomorphicForm

theorem UpperTheory.ConvolutionTheory.R2.Pp.whittaker_eq {F : Type} [Field F] [NumberField F] {f : GL (Fin 2) (A F) → ℂ} (hf : Lf f)
    (g : GL (Fin 2) (A F)) : whittaker f g = Wf f (aE (IdeleGroup.diagonal F (-1)) * g) := by
  letI : Unique (Pos 2) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  rw [← wfT F f hf (-1) g, ← int_one (ι := Pos 2)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have h1 : gl (nU (x default)) = uGL x := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vn, uMat_apply]
    rfl
  have h2 : supSum 0 x = x default := by
    unfold supSum
    rw [Finset.filter_true_of_mem fun p _ => by rw [Unique.eq_default p]; decide, Fintype.sum_unique]
  simp [h1, h2, ψ]

theorem UpperTheory.ConvolutionTheory.R2.Pp.eq_zero_of_Wf {F : Type} [Field F] [NumberField F] {f : GL (Fin 2) (A F) → ℂ}
    (hc : f ∈ cuspForms F 2) (hf : Lf f) (h : ∀ g, Wf f g = 0) : f = 0 := by
  funext g
  rw [eq_nestedWhittaker hc two_pos g]
  simp [nestedWhittaker, whittaker_eq hf, h]
