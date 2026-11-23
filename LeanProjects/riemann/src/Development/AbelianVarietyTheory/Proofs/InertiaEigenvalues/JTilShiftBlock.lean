import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory

theorem jTil_shift_block : ∀ (l n t : ℕ) (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n t h w η typ U → ∀ (a : ZMod n) (S : Set ℚ), (∀ b : ℤ, ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ S) ∧ (U a).count (b + w a) ≤ 1) → ∀ b : ℤ, (if ((b : ℚ) ∈ S ∨ ∃ c : ℕ, c < t ∧ (b : ℚ) = c) then (1 : ℤ) else 0) = tableLineDegreeTwo.jTil U w t a (b + w a) := by
  intro l n t h w η typ U hS a S hU b
  have hsg : 0 ≤ tableLineDegreeTwo.sg n l h a := by
    unfold tableLineDegreeTwo.sg Formalism.WachCohomologyFacts.V2.sgN
    exact Int.floor_nonneg.mpr (tsum_nonneg fun j => by positivity)
  obtain ⟨_, _, _, hG, hB, _, hT2, _⟩ := hS a
  have hblk : (∃ c : ℕ, c < t ∧ (b : ℚ) = c) ↔ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    constructor
    · rintro ⟨c, hc, hbc⟩
      have : b = (c : ℤ) := by exact_mod_cast hbc
      omega
    · rintro ⟨h0, h1⟩
      refine ⟨b.toNat, by omega, ?_⟩
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have hwin : ((w a : ℤ) ≤ b + w a ∧ b + w a ≤ (w a : ℤ) + t - 1) ↔ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> omega
  have hc1 := (hU b).2
  have hcS : (b : ℚ) ∈ S → (U a).count (b + w a) = 1 := (hU b).1.2
  have hcN : (b : ℚ) ∉ S → (U a).count (b + w a) = 0 := fun hn => by
    have := mt (hU b).1.1 hn
    omega
  have hboth : (b : ℚ) ∈ S → ¬ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    rintro hbS ⟨h0, h1⟩
    have hmem : b + (w a : ℤ) ∈ U a := Multiset.count_pos.mp (by rw [hcS hbS]; omega)
    have hlow : b + (w a : ℤ) ∈ tableLineDegreeTwo.lows (typ a) (h a) (η a) (U a) := by
      unfold tableLineDegreeTwo.lows
      rw [Multiset.mem_filter]
      refine ⟨hmem, ?_⟩
      unfold Formalism.WachCohomologyFacts.V2.InWinN
      cases hty : typ a
      · have := hB hty
        simp only [Bool.false_eq_true, if_false]
        constructor <;> omega
      · have := hG hty
        simp only [if_true]
        constructor <;> omega
    have hy : b + (w a : ℤ) ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (w a) t := by
      unfold Formalism.WachCohomologyFacts.Top.GlobalTheory
      rw [Finset.mem_Icc]
      constructor <;> omega
    have := hT2 _ hlow _ hy
    rw [sub_self, abs_zero] at this
    linarith
  unfold tableLineDegreeTwo.jTil
  by_cases hbS : (b : ℚ) ∈ S
  · have hn := hboth hbS
    rw [if_pos (Or.inl hbS), if_neg (by rwa [hwin]), hcS hbS]
    simp
  · rw [hcN hbS]
    by_cases hbl : 0 ≤ b ∧ b ≤ (t : ℤ) - 1
    · rw [if_pos (Or.inr (hblk.2 hbl)), if_pos (hwin.2 hbl)]
      simp
    · rw [if_neg (by rintro (h1 | h1); exact hbS h1; exact hbl (hblk.1 h1)), if_neg (by rwa [hwin])]
      simp

end GlobalTheory
