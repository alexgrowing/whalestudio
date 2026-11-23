import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsMultAtOfSaturated
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtPrimeAtMinimal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

theorem mem_minimalPrimes_of_saturated (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) : Q ∈ J.minimalPrimes := by
  refine ⟨⟨‹Q.IsPrime›, hJQ⟩, fun W hW hWQ q hq => ?_⟩
  obtain ⟨s, hs, hsq⟩ := hsat q hq
  exact (hW.1.mem_or_mem (hW.2 hsq)).resolve_left (fun h => hs (hWQ h))

theorem localizedQuot_map_bijective_of_saturated (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) :
    Function.Bijective (LocalizedModule.map Q.primeCompl
      (Submodule.mapQ J Q LinearMap.id (fun _ ha => hJQ ha) : (A ⧸ J) →ₗ[A] A ⧸ Q)) := by
  refine ⟨?_, LocalizedModule.map_surjective _ _ ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using LocalizedModule.induction_on with | h m s => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [LinearMap.mem_ker, LocalizedModule.map_mk] at hx
    have haQ : a ∈ Q := localizedQuotient_mk_eq_zero Q a s hx
    obtain ⟨t, ht, hta⟩ := hsat a haQ
    rw [Submodule.mem_bot, ← LocalizedModule.zero_mk (1 : Q.primeCompl), LocalizedModule.mk_eq]
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hta
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk J a, rfl⟩

end General

universe u

theorem MultAtOfSaturated.proof : MultAtOfSaturated.Statement.{u} := by
  intro R _ K ι J Q _ hJQ hsat
  refine ⟨mem_minimalPrimes_of_saturated J Q hJQ hsat, ?_⟩
  unfold multAt
  rw [(LinearEquiv.ofBijective _ (localizedQuot_map_bijective_of_saturated J Q hJQ hsat)).length_eq,
    Module.length_eq_one_iff]
  exact localizedQuotient_isSimpleModule Q

end GroundTheory.Heights₂.Heights.NumbersDVR
