import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsBis
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Cap
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Stable
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.Reduce
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.irr :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Irr W M π := by
  intro F E _ _ _ _ _ _ _ D W M π hreg h0 hne
  have hreg' := hreg
  choose m hm _ using hreg'
  have hs : IsStable (span W M π) := UpperTheory.ConvolutionTheory.R2.stable F E D W M π
  have hc : ∀ Φ ∈ span W M π, IsCuspForm Φ := fun Φ hΦ =>
    ⟨UpperTheory.ConvolutionTheory.R2.aut F E D W M π hreg Φ hΦ, (UpperTheory.ConvolutionTheory.R2.cusp F E D W M π h0 Φ hΦ).1⟩
  have hle : span W M π ≤ UpperTheory.V.Cj.S.CI 2 fun τ => m (InfinitePlace.mk (τ.comp (algebraMap F E))) := fun Φ hΦ =>
    UpperTheory.V.Cj.S.mem_CI.2 ⟨hc Φ hΦ, fun τ u => UpperTheory.ConvolutionTheory.R2.cap F E D W M π τ _ (hm _) u Φ hΦ⟩
  have key := UpperTheory.V.TR.SS.le_sSup_minimal (act (E := E) (a := 2)) (span W M π) hs fun U hU hsU => by
    obtain ⟨C, -, c2, c3, c4⟩ := UpperTheory.V.Cj.S.ciCompl (UpperTheory.V.Cj.S.ciBasic UpperTheory.V.Cj.S.capAct) E 2 one_le_two _ U (hU.trans hle) hsU
    refine ⟨C ⊓ span W M π, inf_le_right, fun o x hx => ⟨c2 o x hx.1, hs o x hx.2⟩, ?_, ?_⟩
    · rw [← inf_assoc, c3, bot_inf_eq]
    · rw [← sup_inf_assoc_of_le _ hU, c4, inf_eq_right.2 hle]
  by_contra hno
  refine hne (le_bot_iff.1 (key.trans (sSup_le ?_)))
  rintro V ⟨h1, h2, h3, h4⟩
  exact (hno ⟨⟨V, fun φ hφ => hc φ (h1 hφ), h2, h3, h4⟩, h1⟩).elim
