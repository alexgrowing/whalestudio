import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFlat

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.exists_prime_over :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B →
      (∀ q : Ideal R, q.IsPrime → q ≤ p → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap (algebraMap R B) = q) ∧
      (∀ a : R, algebraMap R B a = 0 → ∃ s : R, s ∉ p ∧ s * a = 0) := by
  intro R _ _ p B _ _ _ h
  haveI := h.isPrime
  haveI := IsCplAt.flat R p B h
  refine ⟨fun q hq hqp => ?_, fun a ha => ?_⟩
  · haveI := hq
    haveI : (maximalIdeal B).LiesOver p := ⟨h.comap_eq.symm⟩
    obtain ⟨P, -, hP, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal B) hqp
    exact ⟨P, hP, hlo.over.symm⟩
  · let Rp := Localization.AtPrime p
    haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
    have hmem : ∀ n : ℕ, algebraMap R Rp a ∈ (maximalIdeal Rp) ^ n := by
      intro n
      obtain ⟨s, hs, hsa⟩ := h.strict n a (by rw [ha]; exact zero_mem _)
      have hu : IsUnit (algebraMap R Rp s) := IsLocalization.map_units Rp (⟨s, hs⟩ : p.primeCompl)
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      have := Ideal.mem_map_of_mem (algebraMap R Rp) hsa
      rw [map_mul] at this
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp this
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal Rp) (IsLocalRing.maximalIdeal.isMaximal Rp).ne_top
    have h0 : algebraMap R Rp a = 0 := by
      have : algebraMap R Rp a ∈ ⨅ i, (maximalIdeal Rp) ^ i := Ideal.mem_iInf.mpr hmem
      rw [hbot] at this
      exact (Ideal.mem_bot).mp this
    obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rp a).mp h0
    exact ⟨s, hs, hsa⟩
