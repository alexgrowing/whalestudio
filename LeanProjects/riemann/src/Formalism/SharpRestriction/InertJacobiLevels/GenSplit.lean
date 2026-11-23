import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField

theorem jacobi_neg_of_one_mod {a g : ℕ} (ha : Odd a) (h4 : g % 4 = 1) (hg : g ≡ 1 [MOD a]) :
    jacobiSym (-(a : ℤ)) g = 1 := by
  have hodd : Odd g := Nat.odd_iff.2 (by omega)
  have h1 : jacobiSym (g : ℤ) a = 1 := by
    have : (g : ℤ) % a = 1 % a := by
      have h2 : g % a = 1 % a := hg
      have h3 : ((g % a : ℕ) : ℤ) = ((1 % a : ℕ) : ℤ) := by rw [h2]
      push_cast at h3
      exact h3
    rw [jacobiSym.mod_left' this, jacobiSym.one_left]
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_one_mod_four h4, one_mul,
    ← jacobiSym.quadratic_reciprocity_one_mod_four h4 ha, h1]

theorem typePrime_facts {q d g : ℕ} (hq : q.Prime) (hd : d.Prime) (hq2 : Odd q) (hd2 : Odd d) (h1 : 1 < g)
    (hg : g ≡ 1 [MOD 16 * q * d]) :
    g ≠ 2 ∧ g ≠ q ∧ g ≠ d ∧ jacobiSym (-(q : ℤ)) g = 1 ∧ jacobiSym (-(d : ℤ)) g = 1 ∧
      (g : ZMod (2 ^ (2 + 2))) = 1 := by
  have h16 : g ≡ 1 [MOD 16] := hg.of_mul_right _ |>.of_mul_right _
  have hmq : g ≡ 1 [MOD q] := by
    have : 16 * q * d = q * (16 * d) := by ring
    rw [this] at hg; exact hg.of_mul_right _
  have hmd : g ≡ 1 [MOD d] := by
    have : 16 * q * d = d * (16 * q) := by ring
    rw [this] at hg; exact hg.of_mul_right _
  have h16' : g % 16 = 1 := h16
  have hne : ∀ p : ℕ, p.Prime → g ≡ 1 [MOD p] → g ≠ p := by
    rintro p hp h rfl
    have : g % g = 1 % g := h
    rw [Nat.mod_self, Nat.mod_eq_of_lt h1] at this
    omega
  refine ⟨by omega, hne q hq hmq, hne d hd hmd, jacobi_neg_of_one_mod hq2 (by omega) hmq,
    jacobi_neg_of_one_mod hd2 (by omega) hmd, ?_⟩
  have := (ZMod.natCast_eq_natCast_iff g 1 (2 ^ (2 + 2))).2 h16
  simpa using this

variable {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1))

theorem hostOf_g_split (u0 : _) (T Lw : ℕ) :
    ∀ k, (placesOver (hostOf A u0 T Lw).E ((hostOf A u0 T Lw).g k)).ncard =
      Module.finrank ℚ (hostOf A u0 T Lw).E := by
  have hM : 1 < 16 * A.q * A.d := by
    nlinarith [Nat.mul_pos A.hyp.1.pos A.hyp.2.1.pos]
  have hc : ∀ g : ℕ, g ≡ 1 [MOD 16 * A.q * A.d] → g % (16 * A.q * A.d) = 1 := by
    intro g hg
    have h1 : g % (16 * A.q * A.d) = 1 % (16 * A.q * A.d) := hg
    rw [Nat.mod_eq_of_lt hM] at h1
    exact h1
  refine g_split_of (hostOf A u0 T Lw) (fun k => ?_)
  fin_cases k
  · exact hc _ A.first_prime_modEq_one
  · exact hc _ A.second_prime_modEq_one

theorem hostOf_tHyp (u0 : _) (T Lw : ℕ) : THyp (hostOf A u0 T Lw) := by
  have hq2 : Odd A.q := Nat.odd_iff.2 (by have := A.hyp.2.2.1; omega)
  have hd2 : Odd A.d := Nat.odd_iff.2 (by have := A.hyp.2.2.2.1; omega)
  have hg0 := A.sixty_one_lt_first_prime
  have hg1 := A.first_prime_lt_second
  have hM : 1 < 16 * A.q * A.d := by
    have := A.hyp.1.pos
    have := A.hyp.2.1.pos
    nlinarith [Nat.mul_pos A.hyp.1.pos A.hyp.2.1.pos]
  have hc : ∀ g : ℕ, g ≡ 1 [MOD 16 * A.q * A.d] → g % (4 * 4 * A.q * A.d) = 1 := by
    intro g hg
    have h1 : g % (16 * A.q * A.d) = 1 % (16 * A.q * A.d) := hg
    rw [Nat.mod_eq_of_lt hM] at h1
    exact h1
  obtain ⟨a0, -, -, -, e0, -⟩ := typePrime_facts A.hyp.1 A.hyp.2.1 hq2 hd2 (by omega) A.first_prime_modEq_one
  obtain ⟨a1, -, -, -, e1, -⟩ := typePrime_facts A.hyp.1 A.hyp.2.1 hq2 hd2 (by omega) A.second_prime_modEq_one
  refine ⟨fun k => ?_, A.bb, fun k => ?_⟩
  · fin_cases k
    · exact hc _ A.first_prime_modEq_one
    · exact hc _ A.second_prime_modEq_one
  · fin_cases k
    · exact ⟨a0, e0⟩
    · exact ⟨a1, e1⟩

end Formalism.MainNotions.Inhab

end
