import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre

namespace GlobalTheory

theorem exists_prime_notMem_ringKrullDim_quotient_eq_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (h : R),
      h ≠ 0 → h ∈ IsLocalRing.maximalIdeal R →
      ∃ q : Ideal R, q.IsPrime ∧ h ∉ q ∧ ringKrullDim (R ⧸ q) = 1 := by
  intro R _ _ _ _ h h0 hhm
  obtain ⟨q, hq, -, h1⟩ := exists_mem_height_map_le_one (IsLocalRing.maximalIdeal R)
    (PrimeSpectrum.basicOpen h).isOpen ⟨⟨⊥, inferInstance⟩, by simpa using h0, bot_le⟩
  have hq' : h ∉ q.asIdeal := hq
  refine ⟨q.asIdeal, q.isPrime, hq', ?_⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hqm : q.asIdeal ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal q.isPrime.ne_top
  have hmax : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have h2 : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro e
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk q.asIdeal) hhm
    rw [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hq' this
  have h3 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  have : IsLocalRing (R ⧸ q.asIdeal) := IsLocalRing.of_surjective' _ hsurj
  have he : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal) =
      IsLocalRing.maximalIdeal (R ⧸ q.asIdeal) := IsLocalRing.eq_maximalIdeal hmax
  rw [he] at h3
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h3]
  rfl

end GlobalTheory
