import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeAndBoundStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

private theorem cast_succ_div_two_of_odd {t : ℕ} (ht : Odd t) :
    (((t + 1) / 2 : ℕ) : ℝ) = ((t : ℝ) + 1) / 2 := by
  obtain ⟨k, rfl⟩ := ht
  have h : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h]
  push_cast
  ring

theorem _root_.GlobalTheory.HTW.wHat_le : ∀ {D : _root_.Formalism.BasicNotions.D7} (L : _root_.Formalism.BasicNotions.SizeData₂ D) (C : ℝ),
    _root_.GlobalTheory.HTW.Roomy L C →
    (_root_.GlobalTheory.HTW.wHat D : ℝ) = _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + (L.etaSz + D.R.t + 2) ≤ 2 * L.sc.b' ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + _root_.GlobalTheory.HTW.sHat L + _root_.GlobalTheory.HTW.etaHat L + 1
      ≤ 2 * L.sc.b' := by
  intro D L C hL
  have hw : (_root_.GlobalTheory.HTW.wHat D : ℝ) =
      _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 := by
    unfold _root_.GlobalTheory.HTW.wHat
    push_cast [cast_succ_div_two_of_odd D.R.t_odd]
    rfl
  have hmax := (_root_.GlobalTheory.HTW.wMax_le_and_ge L C hL).1
  have hR := hL
  unfold _root_.GlobalTheory.HTW.Roomy at hR
  obtain ⟨-, -, h3, h4, -, -⟩ := hR
  have hS := L.Sc_pos
  have hE := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hfS : (_root_.GlobalTheory.HTW.sHat L : ℝ) ≤ L.Sc := by
    unfold _root_.GlobalTheory.HTW.sHat
    exact Nat.floor_le hS.le
  have hfE : (_root_.GlobalTheory.HTW.etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold _root_.GlobalTheory.HTW.etaHat
    push_cast
    linarith [Nat.floor_le hE.le]
  refine ⟨hw, ?_, ?_⟩
  · rw [hw]; nlinarith
  · rw [hw]; nlinarith

end GlobalTheory.HTW
