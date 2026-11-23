import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.MinValClosed

theorem mE_le_padicValNat {l n a : ℕ} (hl : l.Prime) (hn : 2 ≤ n) (he : Even n) (ha : 2 ≤ a)
    (hac : a.Coprime l) : Formalism.PairingDivisionLocalBalance.mE l n ≤ padicValNat l (a ^ n - 1) := by
  haveI := Fact.mk hl
  unfold Formalism.PairingDivisionLocalBalance.mE
  split_ifs with h2 hd
  · subst h2
    have hodd : ¬ 2 ∣ a := by
      intro h
      have := Nat.Coprime.coprime_dvd_left h hac
      norm_num at this
    have ha1 : 1 < a := by omega
    have := padicValNat.pow_two_sub_one_ge ha1 hodd (by omega) he
    omega
  · obtain ⟨k, rfl⟩ := hd
    have hl3 : 3 ≤ l := by have := hl.two_le; omega
    have hk : k ≠ 0 := by rintro rfl; simp at hn
    have hodd : Odd l := hl.odd_of_ne_two h2
    set b := a ^ (l - 1) with hb
    have hb1 : 1 < b := Nat.one_lt_pow (by omega) (by omega)
    have hfer : l ∣ b - 1 := by
      have := Nat.ModEq.pow_card_sub_one_eq_one hl hac
      exact (Nat.modEq_iff_dvd' hb1.le).mp this.symm
    have hnd : ¬ l ∣ b := by
      intro h
      have h1 : l ∣ a := hl.dvd_of_dvd_pow h
      have : l ∣ Nat.gcd a l := Nat.dvd_gcd h1 dvd_rfl
      rw [hac] at this
      exact hl.one_lt.ne' (Nat.dvd_one.mp this)
    have hpow : a ^ ((l - 1) * k) - 1 = b ^ k - 1 ^ k := by rw [pow_mul, one_pow]
    rw [hpow, padicValNat.pow_sub_pow hodd hb1 (by simpa using hfer) hnd hk]
    have hv1 : 1 ≤ padicValNat l (b - 1) := one_le_padicValNat_of_dvd (by omega) hfer
    have hvl : padicValNat l (l - 1) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    rw [padicValNat.mul (by omega) hk, hvl]
    omega
  · exact Nat.zero_le _

theorem mMin_eq_mE : Formalism.PairingDivisionLocalBalance.MinVal → ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n → mMin l n = Formalism.PairingDivisionLocalBalance.mE l n := by
  intro hmv l n hl hn he
  apply le_antisymm
  · obtain ⟨a, ha, hac, hv⟩ := hmv l n hl hn he
    exact Nat.sInf_le ⟨a, ha, hac, hv.symm⟩
  · obtain ⟨a, ha, hac, hv⟩ := mMin_mem hl.one_lt.le n
    rw [hv]
    exact mE_le_padicValNat hl hn he ha hac

end GlobalTheory.MinValClosed
