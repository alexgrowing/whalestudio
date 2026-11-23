import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.Development

open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

theorem ptp_pow {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M) (hx : 0 < orderOf x) :
    x ^ (ℓ ^ (orderOf x).factorization ℓ) =
      (primeToPart ℓ x) ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  set n := orderOf x with hn
  set L := ℓ ^ n.factorization ℓ with hL
  set m := n / L with hm
  have hcop : Nat.Coprime L m := by
    have := Nat.coprime_ordCompl hℓ hx.ne'
    exact Nat.Coprime.pow_left _ this
  have hnm : L * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have : NeZero m := ⟨by intro h0; rw [h0, mul_zero] at hnm; omega⟩
  set u := (((L : ℕ) : ZMod m)⁻¹).val with hu
  have hmod : L * u ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hu, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one L hcop
  have hptp : primeToPart ℓ x = x ^ (L * u) := rfl
  rw [hptp, ← pow_mul, ← pow_mod_orderOf x L, ← pow_mod_orderOf x (L * u * L)]
  congr 1
  show L ≡ L * u * L [MOD orderOf x]
  rw [← hn, ← hnm]
  have := Nat.ModEq.mul_left' L hmod
  rw [mul_one] at this
  rw [mul_comm (L * u) L]
  exact this.symm

theorem ptp_eq_imp {M : Type*} [CommMonoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x y : M)
    (hx : 0 < orderOf x) (hy : 0 < orderOf y) (h : primeToPart ℓ x = primeToPart ℓ y) :
    ∃ j, x ^ (ℓ ^ j) = y ^ (ℓ ^ j) := by
  refine ⟨(orderOf x).factorization ℓ + (orderOf y).factorization ℓ, ?_⟩
  rw [pow_add, pow_mul, ptp_pow ℓ hℓ x hx, h, ← pow_mul, mul_comm, pow_mul,
    ← ptp_pow ℓ hℓ y hy, ← pow_mul, ← pow_add, add_comm]

open Classical in

theorem card_ppRoots_le {K : Type*} [Field K] (N : ℕ) (hN : 2 ≤ N) :
    ((Polynomial.nthRootsFinset N (1 : K)).filter
      (fun y => ∃ ℓ, ℓ.Prime ∧ ∃ j, y ^ (ℓ ^ j) = 1)).card ≤ ppSum N := by
  have hN0 : 0 < N := by omega
  have hsub : (Polynomial.nthRootsFinset N (1 : K)).filter
      (fun y => ∃ ℓ, ℓ.Prime ∧ ∃ j, y ^ (ℓ ^ j) = 1) ⊆
      N.primeFactors.biUnion (fun p => Polynomial.nthRootsFinset (p ^ N.factorization p) (1 : K)) := by
    intro y hy
    rw [Finset.mem_filter, Polynomial.mem_nthRootsFinset hN0] at hy
    obtain ⟨hyN, ℓ, hℓ, j, hj⟩ := hy
    rw [Finset.mem_biUnion]
    have hdvd : orderOf y ∣ ℓ ^ j := orderOf_dvd_of_pow_eq_one hj
    obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
    have hoN : orderOf y ∣ N := orderOf_dvd_of_pow_eq_one hyN
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    ·
      have hy1 : y = 1 := by
        rw [h0, pow_zero, orderOf_eq_one_iff] at hoi; exact hoi
      refine ⟨N.minFac, ?_, ?_⟩
      · exact Nat.mem_primeFactors.2 ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd N, by omega⟩
      · rw [Polynomial.mem_nthRootsFinset (pow_pos (Nat.minFac_pos N) _), hy1, one_pow]
    · have hℓN : ℓ ^ i ∣ N := hoi ▸ hoN
      have hmem : ℓ ∈ N.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hℓ, (dvd_pow_self ℓ hpos.ne').trans hℓN, by omega⟩
      refine ⟨ℓ, hmem, ?_⟩
      rw [Polynomial.mem_nthRootsFinset (pow_pos hℓ.pos _)]
      rw [← orderOf_dvd_iff_pow_eq_one, hoi]
      exact pow_dvd_pow ℓ ((hℓ.pow_dvd_iff_le_factorization (by omega)).1 hℓN)
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  unfold ppSum
  refine Finset.sum_le_sum (fun p hp => ?_)
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

end PI.SqfRootShift.W
