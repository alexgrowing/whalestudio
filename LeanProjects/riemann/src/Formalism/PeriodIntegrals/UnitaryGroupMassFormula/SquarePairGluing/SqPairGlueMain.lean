import Mathlib
import Formalism.PeriodIntegrals.SqPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.ExistsDenLe

noncomputable section
open NumberField Matrix

namespace PI.SqPairW

open Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem crt_exists (R : Subring (Matrix (Fin N) (Fin N) E)) (f : ℕ → Matrix (Fin N) (Fin N) E) (K : ℕ)
    (S : Finset ℕ) : (∀ p ∈ S, p.Prime) → (∀ p ∈ S, f p ∈ R) →
    ∃ e ∈ R, ∀ p ∈ S, ∃ d ∈ R, e = f p + ((p : ℤ) ^ K) • d := by
  intro hprime hf
  classical
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ → ℤ, Q = fun p => ∏ q ∈ S.erase p, ((q : ℤ) ^ K) := ⟨_, rfl⟩
  have hcop : ∀ p ∈ S, ∃ a b : ℤ, a * (p : ℤ) ^ K + b * Q p = 1 := by
    intro p hp
    have h : IsCoprime ((p : ℤ) ^ K) (Q p) := by
      rw [hQdef]
      apply IsCoprime.prod_right
      intro q hq
      apply IsCoprime.pow
      exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (hprime p hp)
        (hprime q (Finset.mem_of_mem_erase hq))).2 (Finset.ne_of_mem_erase hq).symm)
    exact h
  choose! a b hab using hcop
  refine ⟨∑ q ∈ S, (b q * Q q) • f q, ?_, ?_⟩
  · exact sum_mem fun q hq => zsmul_mem (hf q hq) _
  · intro p hp
    have hdiv : ∀ q ∈ S.erase p, ∃ t : ℤ, Q q = (p : ℤ) ^ K * t := by
      intro q hq
      have hm : p ∈ S.erase q := Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hq).symm, hp⟩
      have hd := Finset.dvd_prod_of_mem (fun r : ℕ => ((r : ℤ) ^ K)) hm
      rw [hQdef]
      exact hd
    choose! t ht using hdiv
    refine ⟨(-a p) • f p + ∑ q ∈ S.erase p, (b q * t q) • f q,
      add_mem (zsmul_mem (hf p hp) _)
        (sum_mem fun q hq => zsmul_mem (hf q (Finset.mem_of_mem_erase hq)) _), ?_⟩
    have hsplit := Finset.add_sum_erase S (fun q => (b q * Q q) • f q) hp
    rw [← hsplit]
    have e1 : b p * Q p = 1 + (p : ℤ) ^ K * (-a p) := by linear_combination hab p hp
    have e2 : ∑ q ∈ S.erase p, (b q * Q q) • f q
        = ((p : ℤ) ^ K) • ∑ q ∈ S.erase p, (b q * t q) • f q := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [smul_smul, ht q hq]
      congr 1
      ring
    rw [e2, e1, add_smul, one_smul, smul_add, smul_smul, add_assoc]

theorem sqPairGlue_main : PI.SqPair.PLocalAll → SplitPairGen := by
  intro hP E _ _ _ hCM N L' L'' hN hL' hL'' n hn
  have hloc := hP E hCM N L' L'' hN hL' hL'' n hn
  unfold PI.SqPair.PLocal at hloc
  choose! f hf1 hf2 hf3 using hloc
  have hstar : ∀ x ∈ lam L' L'', xᴴ ∈ lam L' L'' := fun x hx => conjTranspose_mem_lam hL' hL'' hx
  obtain ⟨D, hD0, hD⟩ := exists_den hL' hL'' hn
  obtain ⟨e, heR, he⟩ := crt_exists (lam L' L'') f D D.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (fun p hp => ⟨hf1 p (Nat.prime_of_mem_primeFactors hp),
      hf2 p (Nat.prime_of_mem_primeFactors hp)⟩)
  refine ⟨e, heR.1, heR.2, ?_⟩
  intro M hM y hy

  have himg : ∀ r ∈ lam L' L'', r *ᵥ y ∈ L' ∨ r *ᵥ y ∈ L'' := by
    intro r hr
    rcases hy with hy | hy
    · exact Or.inl (hr.1 y hy)
    · exact Or.inr (hr.2 y hy)
  have key : M *ᵥ y ∈ yg L' L'' n := by
    apply mem_of_local
    intro p hp
    by_cases hpD : p ∣ D
    · have hpS : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpD, hD0.ne'⟩
      obtain ⟨d, hdR, hed⟩ := he p hpS
      rw [hed] at hM
      obtain ⟨M', hM', r, hrR, hMr⟩ := mset_cong hstar ⟨hf1 p hp, hf2 p hp⟩ hdR ((p : ℤ) ^ D) M hM
      obtain ⟨s, hps, m, hm1, hm2, hsm⟩ := hf3 p hp M' hM' y hy
      have hs : s • (M' *ᵥ y) ∈ yg L' L'' n := by
        rw [← Int.cast_smul_eq_zsmul E, hsm]
        exact ⟨m, hm1, hm2, rfl⟩
      have hr : (D : ℤ) • (r *ᵥ y) ∈ yg L' L'' n := hD _ (himg r hrR)
      obtain ⟨a, D', hpD', hDa⟩ := Nat.exists_eq_pow_mul_and_not_dvd hD0.ne' p hp.ne_one
      have ha : a ≤ D := by
        have h1 : p ^ a ≤ D := Nat.le_of_dvd hD0 ⟨D', hDa⟩
        have h2 : a < p ^ a := Nat.lt_pow_self hp.one_lt
        omega
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      refine ⟨s * D', ?_, ?_⟩
      · intro hdvd
        rcases hpZ.dvd_or_dvd hdvd with h | h
        · exact hps h
        · exact hpD' (Int.natCast_dvd_natCast.mp h)
      · have e1 : (s * (D' : ℤ)) • (M *ᵥ y) =
            (D' : ℤ) • (s • (M' *ᵥ y)) + (s * (p : ℤ) ^ (D - a)) • ((D : ℤ) • (r *ᵥ y)) := by
          have hpow : (p : ℤ) ^ D = (p : ℤ) ^ (D - a) * (p : ℤ) ^ a := by
            rw [← pow_add, Nat.sub_add_cancel ha]
          have hDZ : (D : ℤ) = (p : ℤ) ^ a * (D' : ℤ) := by rw [hDa]; push_cast; ring
          rw [hMr, add_mulVec, smul_mulVec, hpow, hDZ]
          module
        rw [e1]
        exact (yg L' L'' n).add_mem ((yg L' L'' n).zsmul_mem hs _) ((yg L' L'' n).zsmul_mem hr _)
    · refine ⟨D, fun h => hpD (Int.natCast_dvd_natCast.mp h), ?_⟩
      exact hD _ (himg M (mset_sub hstar heR M hM))
  obtain ⟨m, h1, h2, h3⟩ := key
  exact ⟨m, h1, h2, h3⟩

end PI.SqPairW
