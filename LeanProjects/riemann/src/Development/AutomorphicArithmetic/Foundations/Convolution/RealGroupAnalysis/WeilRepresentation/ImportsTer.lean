import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.HomCommTrivial
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.gen :
    ∀ (F : Type) [Field F] [NumberField F], St.Gen F := by
  intro F _ _
  refine ⟨eq_top_of_nU_wW _ (fun b => Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)) (Subgroup.subset_closure (Or.inr rfl)),
    le_antisymm ((Subgroup.closure_le _).2 ?_)
      (Gam_le _ (fun b => Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)) (Subgroup.subset_closure (Or.inr rfl)))⟩
  rintro _ (⟨b, rfl⟩ | rfl)
  exacts [nU_rt_mem b, wW_mem]
