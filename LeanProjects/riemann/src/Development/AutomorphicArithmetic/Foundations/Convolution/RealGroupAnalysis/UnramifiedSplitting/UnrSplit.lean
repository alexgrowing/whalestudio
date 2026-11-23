import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsSide
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

open private satLocFree from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
open private UpperTheory.V.Af.RealLocalComponent.exists_comp UpperTheory.V.Af.RealLocalComponent.isotypic from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR

theorem UpperTheory.ConvolutionTheory.R2.H.unrSplit :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ThetaLiftTrivialOrbitTermsVanish W M π → ∀ Q : CuspSub E 2, Q.V ≤ span W M π →
      ∀ (v : P F) (w : P E), SplitAt v w → ∀ B, π.HasSat v B → (CG.mk Q).HasSat w B := by
  intro F E _ _ _ _ _ _ _ D W M π hN Q hQ v w hs B hB
  obtain ⟨hq, i, hc, hx, hv⟩ := hs
  obtain ⟨σ, hσ⟩ := UpperTheory.V.Af.RealLocalComponent.exists_comp UpperTheory.V.Af.admissibleReal π v
  have hiso := UpperTheory.V.Af.RealLocalComponent.isotypic π v σ hσ
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL E 2 Q w
  obtain ⟨e, he⟩ := UpperTheory.ConvolutionTheory.R2.split F E D W M π hN Q hQ v w i hc hx σ σ' hσ hσ'
  have h1 : GlobalTheory.LFun.HasSatGL v σ.ρ B := ((satLocFree F 2 v σ).2 _ π.finPart hiso B).1 hB
  have hq' : Formalism.UG.qV E w = Formalism.UG.qV F v := by
    simpa [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV] using hq
  have h2 : GlobalTheory.LFun.HasSatGL w σ'.ρ B :=
    GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hv hq' e (fun g x => (he g x).symm) h1
  exact (GlobalTheory.BcSpehCompare.hasSat_iff hσ' B).2 h2
