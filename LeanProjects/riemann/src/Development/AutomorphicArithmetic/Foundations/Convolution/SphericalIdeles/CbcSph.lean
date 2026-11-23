import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.TwoLeAbsNorm
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places

open NumberField IsDedekindDomain

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem UpperTheory.ConvolutionTheory.Sph.cbcSph :
    UpperTheory.ConvolutionTheory.Sph.CBCsph := by
  intro K M _ _ _ _ _ _ hp hK n hn π P hW v hv
  haveI := hK
  haveI hM : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  rcases π with @⟨_, π⟩ | @⟨hR, π⟩
  swap
  · exact (not_both K hR hK).elim
  rcases P with @⟨_, P⟩ | @⟨hR, P⟩
  swap
  · exact (not_both M hR hM).elim
  have hu : UpperTheory.ConvolutionTheory.GM.Unr M v := fun w =>
    hv w.1 (HeightOneSpectrum.ext (Ideal.LiesOver.over (P := w.1.asIdeal) (p := v.asIdeal)).symm)
  have hn' : 0 < n := hn
  exact ⟨fun B hB w hw f hf => UpperTheory.ConvolutionTheory.Sph.up K M σ hσ hp n hn' π P hW v hu B hB w hw f hf,
    fun h => UpperTheory.ConvolutionTheory.Sph.down K M σ hσ hp n hn' π P hW v hu h⟩
