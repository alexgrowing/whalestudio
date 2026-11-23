import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila

namespace GlobalTheory.FewBadChars

open Formalism.HermitianLattices.GL2PrimeSums

theorem badChars_count_of_density : GlobalTheory.Mem.An.Jutila → ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
    (((Formalism.HermitianLattices.GL2PrimeSums.BadChars Q).encard : ℕ∞) : ENNReal) ≤ ENNReal.ofReal (C * Q ^ ((1 : ℝ) / 4)) := by
  intro h
  obtain ⟨c, hc⟩ := h 1 one_pos
  refine ⟨|c| + 1, by positivity, fun Q hQ => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have h2 := hc (1 - 1 / 400) Q Q (by norm_num) (by norm_num) hQ1 hQ1
  set Z : Set ((Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ) :=
    {p | 1 ≤ p.1.1 ∧ ((p.1.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.1.2.IsPrimitive ∧
        1 - 1 / 400 ≤ p.2.re ∧ |p.2.im| ≤ Q ∧ DirichletCharacter.LFunction p.1.2 p.2 = 0} with hZ
  have hsub : BadChars Q ⊆ insert (⟨0, 1⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) (Prod.fst '' Z) := by
    rintro ⟨q, χ⟩ ⟨h1, h2, -, h4⟩
    unfold GoodFor at h4
    push Not at h4
    obtain ⟨s, hs1, hs2, hs3⟩ := h4
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · left
      congr 1
      exact DirichletCharacter.level_one χ
    · right
      refine ⟨(⟨q, χ⟩, s), ⟨hq, h1, h2, hs1.le, hs2, ?_⟩, rfl⟩
      exact hs3.2
  have h1 : (BadChars Q).encard ≤ Z.encard + 1 :=
    (Set.encard_le_encard hsub).trans ((Set.encard_insert_le _ _).trans
      (add_le_add (Set.encard_image_le _ _) le_rfl))
  have hq4 : (1 : ℝ) ≤ Q ^ ((1 : ℝ) / 4) := Real.one_le_rpow hQ1 (by norm_num)
  have h3 : (Q ^ 2 * Q) ^ (((2 : ℝ) + 1) * (1 - (1 - 1 / 400))) ≤ Q ^ ((1 : ℝ) / 4) := by
    rw [← pow_succ, ← Real.rpow_natCast, ← Real.rpow_mul hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have h4 : c * (Q ^ 2 * Q) ^ (((2 : ℝ) + 1) * (1 - (1 - 1 / 400))) ≤ |c| * Q ^ ((1 : ℝ) / 4) :=
    mul_le_mul (le_abs_self c) h3 (by positivity) (abs_nonneg c)
  calc (((BadChars Q).encard : ℕ∞) : ENNReal) ≤ ((Z.encard + 1 : ℕ∞) : ENNReal) := ENat.toENNReal_le.mpr h1
    _ = ((Z.encard : ℕ∞) : ENNReal) + 1 := by simp
    _ ≤ ENNReal.ofReal (|c| * Q ^ ((1 : ℝ) / 4)) + ENNReal.ofReal (Q ^ ((1 : ℝ) / 4)) :=
        add_le_add (h2.trans (ENNReal.ofReal_le_ofReal h4)) (ENNReal.one_le_ofReal.mpr hq4)
    _ = ENNReal.ofReal ((|c| + 1) * Q ^ ((1 : ℝ) / 4)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end GlobalTheory.FewBadChars
