import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorRadical
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.RegularLocalRing
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

namespace FunctorialResolution.EmbeddedResolution

theorem isPrime_span_singleton_algebraMap_etaleChartCoord (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (j : Fin m)
    (hj : etaleChartCoord k m S j ∈ q) :
    (Ideal.span ({algebraMap S A (etaleChartCoord k m S j)} : Set A)).IsPrime := by
  have : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hJ : ∀ i ∈ ({j} : Finset (Fin m)), etaleChartCoord k m S i ∈ q := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact hj
  have hJA : ∀ i ∈ ({j} : Finset (Fin m)),
      algebraMap S A (etaleChartCoord k m S i) ∈ IsLocalRing.maximalIdeal A := by
    intro i hi
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q _).mpr (hJ i hi)
  have hli := linearIndependent_toCotangent_etaleChartCoord k m S q A {j} hJ hJA
  exact IsRegularLocalRing.isPrime_span_singleton
    (fun i : { x : Fin m // x ∈ ({j} : Finset (Fin m)) } =>
      algebraMap S A (etaleChartCoord k m S (i : Fin m)))
    (fun i => hJA (i : Fin m) i.2) hli ⟨j, Finset.mem_singleton_self j⟩

end FunctorialResolution.EmbeddedResolution
