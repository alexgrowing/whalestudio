import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
open NumberField IsDedekindDomain

namespace GlobalTheory.InertiaEigenvalues.UnramPlace

theorem exists_place_below : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (l : ℕ), l.Prime → ∀ la : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt φ {la} → ∃ p : HeightOneSpectrum (𝓞 K), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below φ {la} = {p} ∧ ((l : ℕ) : 𝓞 K) ∈ p.asIdeal ∧ ∀ x : K, la.valuation L (φ x) = p.valuation K x := by
  intro K L _ _ _ _ φ l _ la hl hun
  letI : Algebra K L := φ.toAlgebra
  have hmap : RingOfIntegers.mapRingHom φ = algebraMap (𝓞 K) (𝓞 L) := by
    ext x; rfl
  refine ⟨la.under (𝓞 K), ?_, ?_, ?_⟩
  · ext q
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
    rw [hmap]
    exact ⟨fun h => HeightOneSpectrum.ext h, fun h => h ▸ rfl⟩
  · show ((l : ℕ) : 𝓞 K) ∈ la.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
    rw [Ideal.mem_comap, map_natCast]
    exact hl
  · intro x
    have hu := hun la rfl
    rw [hmap] at hu
    have : la.asIdeal.LiesOver (la.under (𝓞 K)).asIdeal := ⟨rfl⟩
    have he : (la.under (𝓞 K)).asIdeal.ramificationIdx' la.asIdeal = 1 := by
      refine Ideal.ramificationIdx'_spec ?_ ?_
      · rw [pow_one]; exact Ideal.map_comap_le
      · exact hu
    have h := HeightOneSpectrum.valuation_liesOver L (la.under (𝓞 K)) la x
    rw [he, pow_one] at h
    exact h.symm

end GlobalTheory.InertiaEigenvalues.UnramPlace
