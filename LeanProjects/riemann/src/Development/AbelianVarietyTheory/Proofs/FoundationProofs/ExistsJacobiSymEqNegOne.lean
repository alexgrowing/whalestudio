import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset

namespace GlobalTheory.JacobiClassSum

theorem exists_jacobiSym_eq_neg_one {s : ℕ} (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s) :
    ∃ c : ℕ, jacobiSym (c : ℤ) s = -1 := by
  obtain ⟨p, hp, t, rfl⟩ := Nat.exists_prime_and_dvd (ne_of_gt h1)
  have hcop : Nat.Coprime p t := Nat.coprime_of_squarefree_mul hsq
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_odd_iff_even.mpr (even_two_mul t)) hodd
  have ht : t ≠ 0 := by
    rintro rfl
    simp at h1
  haveI : NeZero t := ⟨ht⟩
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop n.val 1
  refine ⟨c, ?_⟩
  have e1 : jacobiSym (c : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    have : (((c : ℤ) : ZMod p)) = n := by
      rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc1, ZMod.natCast_zmod_val]
    rwa [this]
  have e2 : jacobiSym (c : ℤ) t = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast (Int.natCast_modEq_iff.mpr hc2)),
      jacobiSym.one_left]
  rw [jacobiSym.mul_right, e1, e2]
  norm_num

theorem jacobiSym_val_natCast {s : ℕ} [NeZero s] (b : ℕ) :
    jacobiSym (((b : ZMod s).val : ℕ) : ℤ) s = jacobiSym (b : ℤ) s := by
  rw [ZMod.val_natCast, Int.natCast_mod, ← jacobiSym.mod_left]

theorem sum_zmod_eq_zero {s : ℕ} [NeZero s] (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s) :
    ∑ x : ZMod s, jacobiSym ((x.val : ℕ) : ℤ) s = 0 := by
  obtain ⟨c, hc⟩ := exists_jacobiSym_eq_neg_one h1 hodd hsq
  have hcop : Nat.Coprime c s := by
    by_contra h
    have : jacobiSym (c : ℤ) s = 0 :=
      jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Int.gcd_natCast_natCast] using h)
    rw [this] at hc
    norm_num at hc
  have key : ∀ x : ZMod s, jacobiSym ((((c : ZMod s) * x).val : ℕ) : ℤ) s
      = - jacobiSym ((x.val : ℕ) : ℤ) s := by
    intro x
    have : (c : ZMod s) * x = ((c * x.val : ℕ) : ZMod s) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [this, jacobiSym_val_natCast, Nat.cast_mul, jacobiSym.mul_left, hc]
    ring
  have h := Equiv.sum_comp (Units.mulLeft (ZMod.unitOfCoprime c hcop))
    (fun x : ZMod s => jacobiSym ((x.val : ℕ) : ℤ) s)
  simp only [Units.mulLeft_apply, ZMod.coe_unitOfCoprime, key, Finset.sum_neg_distrib] at h
  linarith

theorem lamSumZero : Formalism.HermitianLattices.GL2a2.LamSumZero := by
  intro m₀ s a₀ hm h1 hodd hsq hcop
  haveI : NeZero s := ⟨by omega⟩
  rw [← sum_zmod_eq_zero h1 hodd hsq]
  refine Finset.sum_bij (fun b _ => (b : ZMod s)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro b hb b' hb' h
    simp only [Finset.mem_filter, Finset.mem_range] at hb hb'
    have h2 : b ≡ b' [MOD s] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
    have h3 : b ≡ b' [MOD m₀] := hb.2.trans hb'.2.symm
    have h4 : b ≡ b' [MOD m₀ * s] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp ⟨h3, h2⟩
    exact Nat.ModEq.eq_of_lt_of_lt h4 hb.1 hb'.1
  · intro x _
    have hlt := Nat.chineseRemainder_lt_mul hcop.symm a₀ x.val hm.ne' (NeZero.ne s)
    have hpr := (Nat.chineseRemainder hcop.symm a₀ x.val).2
    refine ⟨(Nat.chineseRemainder hcop.symm a₀ x.val : ℕ), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt, hpr.1⟩
    · show ((Nat.chineseRemainder hcop.symm a₀ x.val : ℕ) : ZMod s) = x
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hpr.2, ZMod.natCast_zmod_val]
  · intro b _
    exact (jacobiSym_val_natCast b).symm

end GlobalTheory.JacobiClassSum
