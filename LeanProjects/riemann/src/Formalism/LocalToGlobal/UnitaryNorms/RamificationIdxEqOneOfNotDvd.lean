import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

open NumberField Ideal

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem ne_two_and_ne_q_and_ne_d_of_not_dvd_condN (p : ℕ) (hnd : ¬ p ∣ H.condN) : p ≠ 2 ∧ p ≠ H.q ∧ p ≠ H.d := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    exact hnd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left H.two_dvd_QS _) _)
  · rintro rfl
    exact hnd (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  · rintro rfl
    exact hnd (dvd_mul_left _ _)

theorem span_isPrime (p : ℕ) [hp : Fact p.Prime] : (span {(p : ℤ)}).IsPrime := by
  exact (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)

theorem inertia_trivial (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 :=
  (H.der.frob p hnd P).2.2.2 σ

theorem ramificationIdxIn_eq_one (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN) :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 H.E) = 1 := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hne : (span {(p : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : (span {(p : ℤ)}).IsPrime := span_isPrime p
  haveI : (span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H.E) (span {(p : ℤ)})
  haveI := hQm.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) Q (H.E ≃ₐ[ℚ] H.E),
    ← Formalism.TwoAdicCyclotomicDecomposition.odd_card H.E p Q]
  have hbot : Q.inertia (H.E ≃ₐ[ℚ] H.E) = ⊥ := by
    ext σ
    rw [Subgroup.mem_bot]
    exact AddSubgroup.mem_inertia.trans (inertia_trivial H p hnd Q σ)
  rw [hbot, Subgroup.card_bot]

theorem ramificationIdx_eq_one (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] : P.ramificationIdx ℤ = 1 := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hbot : P.inertia (H.E ≃ₐ[ℚ] H.E) = ⊥ := by
    ext σ
    rw [Subgroup.mem_bot]
    exact AddSubgroup.mem_inertia.trans (inertia_trivial H p hnd P σ)
  rw [← Formalism.TwoAdicCyclotomicDecomposition.odd_card H.E p P, hbot, Subgroup.card_bot]

theorem ramificationIdx_eq_one_of_not_dvd (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] : P.ramificationIdx ℤ = 1 := by
  exact ramificationIdx_eq_one H p hnd P

theorem ramificationIdx'_eq_one (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (span {(p : ℤ)}).ramificationIdx' P = 1 := by
  have hne : (span {(p : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P hne]
  exact ramificationIdx_eq_one H p hnd P

theorem map_eq_mul_coprime (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [hP : P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    ∃ I : Ideal (𝓞 H.E), (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) = P * I ∧ ¬ I ≤ P := by
  have hle : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.LiesOver.over)
  obtain ⟨I, hI⟩ := (Ideal.dvd_iff_le).2 hle
  refine ⟨I, hI, fun hIP => ?_⟩
  have h1 := ramificationIdx'_eq_one H p hnd P
  have h2 : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≤ P ^ 2 := by
    rw [hI, pow_two]
    exact Ideal.mul_mono_right hIP
  exact (Ideal.ramificationIdx'_ne_one_iff hle).2 h2 h1

end Formalism.L2.Host
