import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open private UpperTheory.V.Af.RealLocalComponent.isotypic from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR

theorem UpperTheory.ConvolutionTheory.R2.Pp.isotyp :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.Isotyp F := by
  intro F _ _ _ π v σ h x
  have h1 := (UpperTheory.V.Af.RealLocalComponent.isotypic π v σ h).2
  refine (show (⊤ : Submodule ℂ π.V) ≤ _ from h1 ▸ iSup_le fun f => ?_) Submodule.mem_top
  exact fun y hy => Submodule.subset_span ⟨f.1, f.2, hy⟩
