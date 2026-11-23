import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealMulAbsNormCpowEqExpTsum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLSeriesEqSumPrincipalPartialSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStripsStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeStrip

theorem completedLBoundedInStrips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  intro E _ _ _ I _ φ hφ χ n hu hi hn
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar E χ hu
  have hβ : ∀ β : 𝓞 E, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : E) := by
    intro β h0 h1
    have h0' : (β : E) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, hi (Units.mk0 _ h0')]
    simp only [wt, Units.val_mk0, zpow_neg, Finset.prod_inv_distrib]
  have hle : ∀ a, ‖X a‖ ≤ 1 := fun a => by
    by_cases ha : a = ⊥
    · simp [ha, hX0]
    by_cases ha' : a ⊔ m = ⊤
    · exact (hXn a ha ha').le
    · simp [hXz a ha']
  obtain ⟨r, c, B, M, F, hB, hM, hper, hinv, hdec⟩ := GlobalTheory.T.heckeLSeries_eq_sum_principalPartialSeries E I φ n m X hm hX0 hXm hXn hXz hβ
  choose Λ hΛd hΛb hΛe using fun k => GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips E I φ hφ n hn (M k) (F k) (hM k) (hper k) (hinv k)
  have hB0 : ∀ k, ((B k : ℕ) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hB k).ne'
  refine ⟨fun s => ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * Λ k s, ⟨?_, fun s hs => ?_⟩, ?_⟩
  · intro s
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((differentiableAt_const _).mul ((differentiableAt_id.const_cpow (Or.inl (hB0 k))))).mul ((hΛd k).differentiableAt)
  · refine ⟨∑' a : Ideal (𝓞 E), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s), ?_, ?_⟩
    · rw [GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum E X hX0 hX1 hXm hle s hs]
      convert GlobalTheory.HeckeOne.hasProd_exp hu hs using 1
      simp only [hXP, GlobalTheory.HeckeOne.cf]
    · rw [hdec s hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hΛe k s hs]
      ring
  · intro a b hab
    choose C hC using fun k => hΛb k a b hab
    refine ⟨∑ k, ‖c k‖ * ((B k : ℝ) ^ b * |C k|), fun s h1 h2 => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_natCast_cpow_of_pos (hB k)]
    have hB1 : (1 : ℝ) ≤ (B k : ℝ) := by exact_mod_cast hB k
    gcongr
    exact (hC k s h1 h2).trans (le_abs_self _)

end GlobalTheory.HeckeStrip
