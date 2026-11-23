import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesFirstTypeAmpSqBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetSecondTypeFamilyAmpSqLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeOfHermitianTermTypesCauchySchwarzStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NonzeroDefect

theorem num_first (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) :
    2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 1)) ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have h1 : q ^ (-((k : ℤ) - 1)) ≤ q ^ (-((k : ℤ) - 2 * r - 5)) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  have hq0 : 0 < q := by linarith
  gcongr
  norm_num

theorem num_second (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) (hk : 4 * r + 7 ≤ k) :
    98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) *
        (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have hq0 : 0 < q := by linarith
  have h1 : (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤ q ^ (-((k : ℤ) - 2 * r - 5)) := by
    rw [← zpow_natCast, ← zpow_mul]
    exact zpow_le_zpow_right₀ (by linarith) (by push_cast; omega)
  gcongr

theorem nonzeroDefect_height_power_absorbs_constants (H : ℝ) (hH : 2 ≤ H) (r : ℕ) :
    H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1)))) ≤
      H ^ (39 * (r + 1) ^ 2) := by
  have h0 : 0 < H := by linarith
  have h9 : (392 : ℝ) ≤ H ^ 9 := by
    calc (392 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ H ^ 9 := by gcongr
  calc H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))))
      = 392 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by ring
    _ ≤ H ^ 9 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by gcongr
    _ = H ^ (9 + (2 * (r + 2) + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1))) := by
        simp only [pow_add H]
    _ ≤ H ^ (39 * (r + 1) ^ 2) := pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.zero_le r])

theorem ampSq_nonzero_defect : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2) * (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ ¬ S.BBzero d Λ
  · obtain ⟨d, Λ, hT, hB⟩ := hex
    have hq : (2 : ℝ) ≤ (S.q : ℝ) := by
      have := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
      exact_mod_cast this
    have hqH : (S.q : ℝ) ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.2.2.1 hB
    have hH : (2 : ℝ) ≤ S.Hp := hq.trans hqH
    have hH0 : (0 : ℝ) ≤ S.Hp := by linarith
    have hq0 : (0 : ℝ) < (S.q : ℝ) := by linarith
    have key := GlobalTheory.T.ampSq_le_of_hermitianTermTypes_cauchySchwarz L r k S hk
      (ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) *
        (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn)
      (fun β => (GlobalTheory.T.hermitianFrames_firstType_ampSq_bound L r k S hk β).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_first _ _ hq hH0 r k)) _))
      (fun β J βJ => (GlobalTheory.T.hermitianDoubleCoset_secondType_family_ampSq_le L r k S hk β J βJ).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_second _ _ hq hH0 r k hk)) _))
    refine key.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact mul_le_mul_of_nonneg_right (nonzeroDefect_height_power_absorbs_constants _ hH r) (by positivity)
  · have h0 : (S.ampSq fun d Λ => ¬ S.BBzero d Λ) = 0 := by
      have ha : ∀ d, S.amp d (fun Λ => ¬ S.BBzero d Λ) = 0 := by
        intro d
        unfold Frames.amp
        have : ∀ Λ, ¬ (S.IsTerm d Λ ∧ ¬ S.BBzero d Λ) := fun Λ h => hex ⟨d, Λ, h⟩
        simp only [this, if_false, tsum_zero]
      unfold Frames.ampSq Frames.sumData
      simp [ha]
    rw [h0]
    exact zero_le

end GlobalTheory.HL.NonzeroDefect
