import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroDefectHeightPowerAbsorbsConstants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeHeightMulMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalSumsEqConstMulCoordinateSumsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCardStatement

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.AbstractBound

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem nn_eq_zero (h : ∀ d Λ, ¬ S.IsTerm d Λ) : S.nn = 0 := by
  simp [Frames.nn, Frames.sumData, Frames.mass, h]

theorem ampSq_BBzero_eq (h : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ) :
    S.ampSq S.BBzero = S.ampSq fun _ _ => True := by
  have : ∀ d, S.amp d (S.BBzero d) = S.amp d (fun _ => True) := by
    intro d
    unfold Frames.amp
    refine tsum_congr fun o => ?_
    by_cases H : S.IsTerm d o.out
    · simp [H, h _ _ H]
    · simp [H]
  simp only [Frames.ampSq, this]

theorem raise [IsNonarchimedeanLocalField F] [CharZero F] {C : ℝ} (hC : 39 ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2) * t) * S.nn ≤
      ENNReal.ofReal (S.Hp ^ (C * ((r : ℝ) + 1) ^ 2) * t) * S.nn := by
  by_cases h : ∃ d Λ, S.IsTerm d Λ
  · obtain ⟨d, Λ, hd⟩ := h
    have h1 : 1 ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hd).2.2.2.2.1
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ ht)) _
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le h1 ?_
    push_cast
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  · push_neg at h
    simp [nn_eq_zero S h]

end

theorem ngAt : ∀ (C : ℝ), 39 ≤ C → ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → LocNG.NGAt k P C := by
  intro C hC F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hV hP R d0
  letI := hM.loc
  letI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hV hP
  obtain ⟨κ, -, e1, e2, e3, e4⟩ := GlobalTheory.T.hermitianLocalSums_eq_const_mul_coordinateSums M hM H r k P S c R d0
  obtain ⟨hH, hq, hpr⟩ := GlobalTheory.T.framePairCoordinates_localHeight_eq_residueCard M hM H r k P S c
  have n1 := GlobalTheory.HL.NonzeroDefect.ampSq_nonzero_defect M.L r k S hk
  obtain ⟨n2, n3⟩ := GlobalTheory.HL.NoCancellation.ampSq_le_height_mul_mass M.L r k S hk
  have r1 := raise S hC (t := 1) zero_le_one
  simp only [mul_one] at r1
  rw [e1, e2, e3, e4, hH, hq]
  refine ⟨?_, ?_, ?_, fun hp => ?_⟩
  · rw [mul_left_comm]
    refine mul_le_mul_right (n1.trans ?_) _
    have : (S.q : ℝ) ^ (-((k : ℝ) - 2 * r - 5)) = (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5)) := by
      rw [← Real.rpow_intCast]; push_cast; rfl
    rw [this]
    exact raise S hC (by positivity)
  · rw [mul_left_comm]
    exact mul_le_mul_right (n2.trans r1) _
  · rw [mul_left_comm]
    exact mul_le_mul_right (n3.trans r1) _
  · obtain ⟨g1, g2, g3⟩ := hpr hp
    obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.HL.GoodPlace.equality M.L r k S hk g1 g2 g3
    rw [ampSq_BBzero_eq S a1, a3]
    exact ⟨a2, rfl, rfl⟩

end GlobalTheory.HL.AbstractBound
