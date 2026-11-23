import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem pow_eq_pow_of_modEq_orderOf {M : Type*} [Monoid M] (x : M) {a b : ℕ}
    (h : a ≡ b [MOD orderOf x]) : x ^ a = x ^ b := by
  rw [← pow_mod_orderOf x a, ← pow_mod_orderOf x b, show a % orderOf x = b % orderOf x from h]

theorem gcd_mul_pow_totient {q m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime q m) :
    Nat.gcd (q * m) (q ^ Nat.totient m) = q := by
  have ht : 0 < Nat.totient m := Nat.totient_pos.mpr hm
  obtain ⟨k, hk⟩ : ∃ k, Nat.totient m = k + 1 := ⟨Nat.totient m - 1, by omega⟩
  rw [hk, pow_succ', Nat.gcd_mul_left]
  have : Nat.gcd m (q ^ k) = 1 := (Nat.Coprime.pow_right k hcop.symm)
  rw [this, mul_one]

theorem prime_to_part_spec : PrimeToPartSpec := by
  unfold PrimeToPartSpec
  intro M _ l x hl hx
  set n := orderOf x with hn
  set q := l ^ n.factorization l with hq
  have hnpos : 0 < n := hx.orderOf_pos
  have hqd : q ∣ n := Nat.ordProj_dvd n l
  have hqpos : 0 < q := pow_pos hl.pos _
  have hmpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hnpos hqd) hqpos
  have hcop : Nat.Coprime q (n / q) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hnpos.ne')
  have hnqm : n = q * (n / q) := (Nat.mul_div_cancel' hqd).symm
  unfold primeToPart
  refine ⟨?_, ?_⟩
  · have hg : Nat.gcd n (q ^ Nat.totient (n / q)) = q := by
      have h3 := gcd_mul_pow_totient hmpos hcop
      rwa [← hnqm] at h3
    rw [orderOf_pow' x (pow_pos hqpos _).ne', ← hn, hg]
  · refine ⟨n.factorization l, ?_⟩
    rw [← pow_mul]
    apply pow_eq_pow_of_modEq_orderOf
    rw [← hn]
    have h1 : q ^ Nat.totient (n / q) ≡ 1 [MOD n / q] := Nat.ModEq.pow_totient hcop
    have h2 : q * q ^ Nat.totient (n / q) ≡ q * 1 [MOD q * (n / q)] := Nat.ModEq.mul_left' q h1
    rw [← hnqm, mul_one, mul_comm] at h2
    exact h2.symm

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
