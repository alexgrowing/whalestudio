import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.CondESpec
import Development.AutomorphicArithmetic.FrobeniusLocalisation.CardImgOneDvd

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem layer_dvd {N l j : ℕ} (hj : j ≤ N.factorization l) : ordCompl[l] N * l ^ j ∣ N := by
  have h := Nat.ordProj_mul_ordCompl_eq_self N l
  conv_rhs => rw [← h, mul_comm]
  exact mul_dvd_mul_left _ (pow_dvd_pow l hj)

private theorem dvd_layer_iff {N c l j : ℕ} (hl : l.Prime) (hN : N ≠ 0) (hc : c ∣ N) :
    c ∣ ordCompl[l] N * l ^ j ↔ c.factorization l ≤ j := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.1 hc)
  have hM : 0 < ordCompl[l] N := Nat.ordCompl_pos l hN
  have hM0 : ordCompl[l] N * l ^ j ≠ 0 := Nat.mul_ne_zero hM.ne' (pow_ne_zero _ hl.ne_zero)
  have hfM : (ordCompl[l] N * l ^ j).factorization = N.factorization.erase l + Finsupp.single l j := by
    rw [Nat.factorization_mul hM.ne' (pow_ne_zero _ hl.ne_zero), Nat.factorization_ordCompl,
      hl.factorization_pow]
  have hcN := (Nat.factorization_le_iff_dvd hc0 hN).2 hc
  rw [← Nat.factorization_le_iff_dvd hc0 hM0, hfM]
  constructor
  · intro h
    have := h l
    simpa using this
  · intro h q
    by_cases hq : q = l
    · subst hq
      simpa using h
    · rw [Finsupp.add_apply, Finsupp.erase_ne hq]
      exact le_add_right (hcN q)

theorem UpperTheory.HF.layer_bot :
    ∀ {φ : Frame} (H : HostRaw φ) {l j : ℕ}, l.Prime → j ≤ H.condN.factorization l → (H.imgOne (ordCompl[l] H.condN * l ^ j) = ⊥ ↔ H.condE.factorization l ≤ j) ∧ (j ≤ H.condE.factorization l → Nat.card (H.imgOne (ordCompl[l] H.condN * l ^ j)) ∣ (l ^ H.condE.factorization l).totient / (l ^ j).totient) ∧ H.condE.factorization l ≤ H.condN.factorization l := by
  intro φ H l j hl hj
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  obtain ⟨hE, hEpos, hspec⟩ := condE_spec H
  have hEN : H.condE.factorization l ≤ H.condN.factorization l :=
    (Nat.factorization_le_iff_dvd hEpos.ne' hN).2 hE l
  have part1 : ∀ k, k ≤ H.condN.factorization l →
      (H.imgOne (ordCompl[l] H.condN * l ^ k) = ⊥ ↔ H.condE.factorization l ≤ k) := by
    intro k hk
    rw [hspec _ (layer_dvd hk)]
    exact dvd_layer_iff hl hN hE
  refine ⟨part1 j hj, fun hje => ?_, hEN⟩
  set e := H.condE.factorization l with he
  have hdiv : ordCompl[l] H.condN * l ^ j ∣ ordCompl[l] H.condN * l ^ e :=
    mul_dvd_mul_left _ (pow_dvd_pow l hje)
  have hc := card_imgOne_dvd H hdiv (layer_dvd hEN)
  rw [(part1 e hEN).2 le_rfl, Subgroup.card_bot, one_mul] at hc
  have hcop : ∀ k, (ordCompl[l] H.condN).Coprime (l ^ k) := fun k =>
    ((Nat.coprime_ordCompl hl hN).pow_left k).symm
  have hM : 0 < ordCompl[l] H.condN := Nat.ordCompl_pos l hN
  rw [Nat.totient_mul (hcop e), Nat.totient_mul (hcop j),
    Nat.mul_div_mul_left _ _ (Nat.totient_pos.2 hM)] at hc
  exact hc
