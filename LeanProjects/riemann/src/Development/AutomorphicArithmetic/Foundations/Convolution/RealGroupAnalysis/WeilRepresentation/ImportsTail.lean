import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.UnrInert
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.UnrSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

open UpperTheory.ConvolutionTheory.R2.H in
theorem UpperTheory.ConvolutionTheory.R2.unr :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Unr W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h0 Q hQ
  have hs : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ v : HeightOneSpectrum (𝓞 F), Below v w → ∃ B, π.HasSat v B := by
    have h1 := UpperTheory.V.Af.Gk.satAE F 2 π
    rw [Filter.eventually_cofinite] at h1 ⊢
    refine (h1.biUnion (t := fun v => {w : HeightOneSpectrum (𝓞 E) | Below v w}) fun v _ => ?_).subset fun w hw => ?_
    · have := v.isMaximal
      refine Set.Finite.of_finite_image (f := fun w => w.asIdeal) ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_)
        fun _ _ _ _ e => HeightOneSpectrum.ext e
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨w.isPrime, ⟨hw⟩⟩
    · simp only [Set.mem_setOf_eq, not_forall] at hw
      obtain ⟨v, hv, hn⟩ := hw
      exact Set.mem_biUnion (show v ∈ {v | ¬ ∃ B, π.HasSat v B} from hn) hv
  filter_upwards [hs, placeAe F E D, unrInert F E D W M π h0 Q hQ] with w h1 h2 h3 v hv f hf
  obtain ⟨B, hB⟩ := h1 v hv
  have h4 : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  refine ⟨B, hB, ?_⟩
  rcases h2 v hv with hsp | hi
  · have : f = 1 := Nat.pow_right_injective h4 (show normV v ^ f = normV v ^ 1 by rw [← hf, hsp.1, pow_one])
    subst this
    simpa using unrSplit F E D W M π h0 Q hQ v w hsp B hB
  · have : f = 2 := Nat.pow_right_injective h4 (show normV v ^ f = normV v ^ 2 by rw [← hf, hi.norm])
    subst this
    exact h3 v hv hi B hB
