import Mathlib
import Formalism.CyclotomicNorms.StatementT
import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms

theorem pow_primeToPart {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x : M) (hx : IsOfFinOrder x) :
    primeToPart ℓ x ^ (ℓ ^ (orderOf x).factorization ℓ) = x ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  set n := orderOf x with hn
  have hn0 : n ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  set a := n.factorization ℓ
  set m := n / ℓ ^ a with hm
  have hnm : ℓ ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hc : Nat.Coprime (ℓ ^ a) m := (Nat.coprime_ordCompl hℓ hn0).pow_left a
  set u := (((ℓ ^ a : ℕ) : ZMod m)⁻¹).val
  have h1 : ((ℓ ^ a * u : ℕ) : ZMod m) = 1 := by
    have hm0 : NeZero m := ⟨fun h => hn0 (by rw [← hnm, h, mul_zero])⟩
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one _ hc
  have h2 : ℓ ^ a * u ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, h1, Nat.cast_one]
  unfold primeToPart
  rw [← pow_mul]
  have h3 : ℓ ^ a * u * ℓ ^ a ≡ ℓ ^ a [MOD n] := by
    have := h2.mul_left' (ℓ ^ a)
    rw [mul_one, hnm] at this
    rwa [mul_comm (ℓ ^ a * u) (ℓ ^ a)]
  rw [← pow_mod_orderOf x (ℓ ^ a * u * ℓ ^ a), ← pow_mod_orderOf x (ℓ ^ a)]
  exact congrArg _ h3

theorem exists_pow_eq {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x y : M) (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : primeToPart ℓ x = primeToPart ℓ y) : ∃ c : ℕ, x ^ ℓ ^ c = y ^ ℓ ^ c := by
  refine ⟨(orderOf x).factorization ℓ + (orderOf y).factorization ℓ, ?_⟩
  have h1 := pow_primeToPart hℓ x hx
  have h2 := pow_primeToPart hℓ y hy
  rw [pow_add, pow_mul, ← h1, h, ← pow_mul, mul_comm, pow_mul, h2, ← pow_mul]

theorem exc_of_dvd {g d e ℓ c : ℕ} (hg : 2 ≤ g) (hℓ : ℓ.Prime) (hd : 1 ≤ d) (he : 2 * Nat.gcd d e ≤ d)
    (h : g ^ d - 1 ∣ ℓ ^ c * (g ^ e - 1)) : Exc g d ℓ := by
  refine ⟨hℓ, ?_⟩
  set G := g ^ d with hG
  have hG3 : 3 ≤ G := by
    have h2 : 2 ≤ d := by
      have : 1 ≤ Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd
      omega
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ g ^ 2 := Nat.pow_le_pow_left hg 2
      _ ≤ g ^ d := Nat.pow_le_pow_right (by omega) h2
  have hn0 : G - 1 ≠ 0 := by omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set v := padicValNat ℓ (G - 1) with hv
  have hfac : (G - 1).factorization ℓ = v := Nat.factorization_def _ hℓ
  set B := (G - 1) / ℓ ^ v with hB
  have hAB : ℓ ^ v * B = G - 1 := by
    have := Nat.ordProj_mul_ordCompl_eq_self (G - 1) ℓ
    rwa [hfac] at this
  have hcop : Nat.Coprime ℓ B := by
    have := Nat.coprime_ordCompl hℓ hn0
    rwa [hfac] at this
  have hB1 : B ∣ g ^ e - 1 :=
    (Nat.Coprime.pow_left c hcop).symm.dvd_of_dvd_mul_left ((Dvd.intro_left _ hAB).trans h)
  have hB2 : B ∣ g ^ Nat.gcd d e - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd (Dvd.intro_left _ hAB) hB1
  set s := Nat.gcd d e
  have hs1 : 1 ≤ s := Nat.gcd_pos_of_pos_left e hd
  have hgs : 2 ≤ g ^ s := le_trans hg (Nat.le_self_pow (by omega) g)
  have hBle : B ≤ g ^ s - 1 := Nat.le_of_dvd (by omega) hB2
  have hBsq : B * B ≤ G - 1 := by
    have h1 : g ^ s * g ^ s ≤ G := by
      rw [← pow_add, hG]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : B * B ≤ (g ^ s - 1) * (g ^ s - 1) := Nat.mul_le_mul hBle hBle
    have h3 : (g ^ s - 1) * (g ^ s - 1) + 1 ≤ g ^ s * g ^ s := by
      obtain ⟨t, ht⟩ : ∃ t, g ^ s = t + 2 := ⟨g ^ s - 2, by omega⟩
      rw [ht]; simp only [show t + 2 - 1 = t + 1 by omega]; nlinarith
    omega
  set A := ℓ ^ v
  have hA2 : G - 1 ≤ A * A := by
    have h1 : (A * A) * (B * B) = (G - 1) * (G - 1) := by rw [← hAB]; ring
    by_contra hlt
    push Not at hlt
    have hBpos : 0 < B * B := by
      rcases Nat.eq_zero_or_pos (B * B) with h0 | h0
      · rw [h0, mul_zero] at h1
        have : 0 < (G - 1) * (G - 1) := Nat.mul_pos (by omega) (by omega)
        omega
      · exact h0
    have : (A * A) * (B * B) < (G - 1) * (G - 1) :=
      calc (A * A) * (B * B) < (G - 1) * (B * B) := Nat.mul_lt_mul_of_pos_right hlt hBpos
        _ ≤ (G - 1) * (G - 1) := Nat.mul_le_mul_left _ hBsq
    omega
  have hA4 : ℓ ^ (4 * v) = (A * A) * (A * A) := by
    show ℓ ^ (4 * v) = (ℓ ^ v * ℓ ^ v) * (ℓ ^ v * ℓ ^ v)
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [hA4]
  have h5 : (G - 1) * (G - 1) ≤ (A * A) * (A * A) := Nat.mul_le_mul hA2 hA2
  have h6 : G < (G - 1) * (G - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, G = t + 3 := ⟨G - 3, by omega⟩
    rw [ht]; simp only [show t + 3 - 1 = t + 2 by omega]; nlinarith
  omega

end Formalism.BasicNotions.Examples₂.NZ
