import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMQuotientUnmixed
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMParameterQuotient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRingUnmixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem map_mem_associatedPrimes_quotient {B : Type*} [CommRing B] [IsNoetherianRing B] (I p : Ideal B)
    (hp : p ∈ associatedPrimes B (B ⧸ I)) :
    I ≤ p ∧ p.map (Ideal.Quotient.mk I) ∈ associatedPrimes (B ⧸ I) (B ⧸ I) := by
  obtain ⟨hprime, a, rfl⟩ := (isAssociatedPrime_iff (I := p) (M := B ⧸ I)).1 hp
  have hI : I ≤ Submodule.colon (⊥ : Submodule B (B ⧸ I)) {a} := fun b hb => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul]
  refine ⟨hI, (isAssociatedPrime_iff).2 ⟨?_, a, ?_⟩⟩
  · exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  · ext c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective, Submodule.mem_colon_singleton]
    constructor
    · rintro ⟨b', hb', hbb'⟩
      rw [← hbb']
      simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using hb'
    · intro h
      exact ⟨b, by simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using h, rfl⟩

theorem CMQuotientUnmixed.proof (hQ : CMParameterQuotient.Statement) (hU : CMRingUnmixed.Statement) :
    CMQuotientUnmixed.Statement := by
  intro B _ _ d x hx hdim p hp
  set I := Ideal.span (Set.range x) with hIdef
  have hCM : IsCohenMacaulayLocalRing (B ⧸ I) := hQ B d x hx hdim
  obtain ⟨hIp, hq⟩ := map_mem_associatedPrimes_quotient I p hp
  obtain ⟨hmin, hdq⟩ := hU (B ⧸ I) _ hq
  have hcomap : (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.2 hIp]
  refine ⟨?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨_, hmin, hcomap⟩
  · rw [← hdq]
    exact (ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIp)).symm

end GroundTheory.Heights₂.Heights
