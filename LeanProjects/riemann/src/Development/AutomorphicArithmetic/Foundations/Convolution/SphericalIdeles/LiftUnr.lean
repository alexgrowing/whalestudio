import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.CbcSph
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftAll
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem UpperTheory.ConvolutionTheory.Sph.liftUnr :
    UpperTheory.ConvolutionTheory.Sph.LiftUnr := by
  intro K M _ _ _ _ _ _ _ _ hp a ha π hη
  obtain ⟨L, -, -⟩ := UpperTheory.ConvolutionTheory.cbcc K M hp inferInstance a ha
  rcases L (.cx π) with ⟨η, hη', e⟩ | ⟨P, hW, hinf, hS⟩
  · exact (hη η hη' (Quotient.sound e)).elim
  rcases P with @⟨_, P⟩ | @⟨hR, P⟩
  swap
  · exact (not_both M hR inferInstance).elim
  refine ⟨P, hW, fun w f B hu hf hB => ?_, fun τ => ?_, hS⟩
  · have hall : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) →
        Algebra.IsUnramifiedAt (𝓞 K) w'.asIdeal := by
      intro w' hw'
      by_contra hr
      obtain ⟨-, h2, -⟩ := UpperTheory.ConvolutionTheory.Sph.normRam K M hp w' hr
      have e' : w = w' := h2 w hw'.symm
      exact hr (e' ▸ hu)
    exact (UpperTheory.ConvolutionTheory.Sph.cbcSph K M hp inferInstance a ha (.cx π) (.cx P) hW (w.under (𝓞 K)) hall).1 B hB w rfl f hf
  · have h := hinf τ _ (ParLaws.hasInfChar_infChar (CG.mk π) (τ.comp (algebraMap K M)))
    exact CG.HasInfChar.infChar_eq (π := CG.mk P) h
