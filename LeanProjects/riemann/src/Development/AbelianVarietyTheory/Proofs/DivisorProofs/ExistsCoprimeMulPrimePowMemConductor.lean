import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.CondNumber

theorem exists_mul_pow_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ M j : ℕ, ¬ l ∣ M ∧ (M : 𝓞 K) * (l : 𝓞 K) ^ j ∈ I := by
  have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨j, M, hM, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  refine ⟨M, j, hM, ?_⟩
  have := Ideal.absNorm_mem I
  rw [he] at this
  push_cast at this
  rwa [mul_comm] at this

theorem mem_of_forall_pow {R : Type} [CommRing R] [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) {x : R}
    (h : ∀ (v : HeightOneSpectrum R) (n : ℕ), v.asIdeal ^ n ∣ I → x ∈ v.asIdeal ^ n) : x ∈ I := by
  have e := Ideal.iInf_maxPowDividing_eq (I := I) hI
  rw [← e, Submodule.mem_iInf]
  intro v
  apply h v
  rw [Ideal.dvd_iff_le]
  exact e.ge.trans (iInf_le _ v)

theorem exists_mem_condQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), l.Prime → IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∃ M : ℕ, ¬ l ∣ M ∧ ((M * l ^ a0 𝔣 l : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  intro E _ _ _ l 𝔣 Q hl h𝔣 hQ
  obtain ⟨M₁, j, hM₁, hj⟩ := exists_mul_pow_mem hl h𝔣.1
  have h1 : (M₁ : OF E) * (l : OF E) ^ a0 𝔣 l ∈ 𝔣 := by
    refine mem_of_forall_pow h𝔣.1 fun v n hn => ?_
    by_cases hv : (l : OF E) ∈ v.asIdeal
    · have hfin : FiniteMultiplicity v.asIdeal 𝔣 :=
        FiniteMultiplicity.of_not_isUnit v.irreducible.not_isUnit h𝔣.1
      have hle : n ≤ a0 𝔣 l :=
        (hfin.le_multiplicity_of_pow_dvd hn).trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_maxConductorExponentOverPrime h𝔣 hv)
      exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hv _))
    · have h2 := Ideal.le_of_dvd hn hj
      have := v.isPrime
      rcases Ideal.IsPrime.mem_pow_mul v.asIdeal h2 with h3 | h3
      · exact Ideal.mul_mem_right _ _ h3
      · exact absurd (v.isPrime.mem_of_pow_mem _ h3) hv
  have h2 : ∀ q : HeightOneSpectrum (OF E), ∃ M : ℕ, ¬ l ∣ M ∧ (q ∈ Q → (M : OF E) ∈ q.asIdeal) := by
    intro q
    obtain ⟨M, i, hM, hi⟩ := exists_mul_pow_mem hl q.ne_bot
    refine ⟨M, hM, fun hq => ?_⟩
    rcases q.isPrime.mem_or_mem hi with h3 | h3
    · exact h3
    · exact absurd (q.isPrime.mem_of_pow_mem _ h3) (hQ q hq)
  choose N hN hNq using h2
  refine ⟨M₁ * ∏ q ∈ Q, N q, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · exact hM₁ h
    · obtain ⟨q, -, hq⟩ := (Prime.dvd_finset_prod_iff hl.prime _).1 h
      exact hN q hq
  · have h3 : (∏ q ∈ Q, (N q : OF E)) ∈ ∏ q ∈ Q, q.asIdeal := Ideal.prod_mem_prod fun q hq => hNq q hq
    have h4 := Ideal.mul_mem_mul h1 h3
    unfold condQ
    convert h4 using 1
    push_cast
    ring

end GlobalTheory.HilbFam.CondNumber
