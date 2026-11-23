import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

open IsLocalRing

theorem modEq_of_pow_modEq_pow_sub_one (l n a b : ℕ) (hl : 2 ≤ l) (hn : 0 < n)
    (h : l ^ a ≡ l ^ b [MOD l ^ n - 1]) : a ≡ b [MOD n] := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have hpos : 1 ≤ l ^ n := Nat.one_le_pow _ _ (by omega)
    have hone : l ^ n ≡ 1 [MOD l ^ n - 1] :=
      ((Nat.modEq_iff_dvd' hpos).2 dvd_rfl).symm
    have hred : ∀ c : ℕ, l ^ c ≡ l ^ (c % n) [MOD l ^ n - 1] := by
      intro c
      conv_lhs => rw [← Nat.div_add_mod c n, pow_add, pow_mul]
      have := (hone.pow (c / n)).mul_right (l ^ (c % n))
      simpa using this
    have hlt : ∀ c : ℕ, l ^ (c % n) < l ^ n - 1 := by
      intro c
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h2 : l ^ (c % (k + 1)) ≤ l ^ k :=
        Nat.pow_le_pow_right (by omega) (Nat.lt_succ_iff.1 (Nat.mod_lt _ hn))
      have h3 : l ^ 1 ≤ l ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : l ^ k * 2 ≤ l ^ k * l := Nat.mul_le_mul_left _ hl
      rw [pow_one] at h3
      rw [pow_succ]
      omega
    have h5 : l ^ (a % n) ≡ l ^ (b % n) [MOD l ^ n - 1] :=
      ((hred a).symm.trans h).trans (hred b)
    have h6 := Nat.ModEq.eq_of_lt_of_lt h5 (hlt a) (hlt b)
    exact Nat.pow_right_injective hl h6
  · obtain rfl : n = 1 := by omega
    exact Nat.modEq_one

theorem exists_frobenius_and_exponent_modEq (l : ℕ) [Fact l.Prime] :
    (∃ φ : GQ l, ∀ n : ℕ, 0 < n → ∀ x : Om l, x ^ l ^ n = x → φ x = x ^ l) ∧
    ∀ n a b : ℕ, 0 < n → (∀ x : Om l, x ^ l ^ n = x → x ^ l ^ a = x ^ l ^ b) →
      a ≡ b [MOD n] := by
  have hp : l.Prime := Fact.out
  have hgt : ∀ n : ℕ, 0 < n → 1 < l ^ n := fun n hn => Nat.one_lt_pow hn.ne' hp.one_lt
  constructor
  · have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
    have : NeZero l := ⟨hp.ne_zero⟩
    have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
      rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
    obtain ⟨φ, hφ⟩ := GlobalTheory.MemLoc.exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
      (Finite.of_equiv _ e.symm.toEquiv) (Om l)
    rw [hcard] at hφ
    refine ⟨φ, fun n hn x hx => ?_⟩
    by_cases h0 : x = 0
    · rw [h0, map_zero, zero_pow hp.ne_zero]
    have h1 := hgt n hn
    refine hφ x (l ^ n - 1) (fun h => ?_) ?_
    · rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
      have h2 : l ∣ l ^ n := dvd_pow_self l hn.ne'
      have h3 : l ∣ l ^ n - (l ^ n - 1) := Nat.dvd_sub h2 h
      have h4 : l ^ n - (l ^ n - 1) = 1 := by omega
      rw [h4] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
    · apply mul_right_cancel₀ h0
      rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]
  · intro n a b hn h
    have h1 := hgt n hn
    have : NeZero (l ^ n - 1) := ⟨by omega⟩
    have : NeZero ((l ^ n - 1 : ℕ) : Om l) := inferInstance
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)
    have h2 : ζ ^ l ^ n = ζ := by
      conv_lhs => rw [← Nat.sub_add_cancel h1.le, pow_succ, hζ.pow_eq_one, one_mul]
    have h3 := h ζ h2
    apply modEq_of_pow_modEq_pow_sub_one l n a b hp.two_le hn
    have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (by omega)
    rw [hζ.eq_orderOf]
    exact hfin.pow_eq_pow_iff_modEq.1 h3

end GlobalTheory.Cyc
