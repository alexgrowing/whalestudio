import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.invVol_eq_div_of_le {G : Type*} [Group G] {D A B : Subgroup G}
    (hA : D ≤ A) (hB : D ≤ B) (h : D.relIndex A ≠ 0) :
    _root_.GlobalTheory.HL.invVol A B = (D.relIndex A : ℝ) / (D.relIndex B : ℝ) := by
  unfold _root_.GlobalTheory.HL.invVol
  have hDC : D ≤ A ⊓ B := le_inf hA hB
  have eA := Subgroup.relIndex_mul_relIndex D (A ⊓ B) A hDC inf_le_left
  have eB := Subgroup.relIndex_mul_relIndex D (A ⊓ B) B hDC inf_le_right
  rw [Subgroup.inf_relIndex_left] at eA
  rw [Subgroup.inf_relIndex_right] at eB
  have ha : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply h
    rw [← eA, h0, zero_mul]
  rw [← eA, ← eB, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr ha)]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.invVol_mul_pos_le_conj : ∀ {G : Type} [Group G] (K0 K1 K : Subgroup G),
    K0.relIndex K1 ≠ 0 → K1.relIndex K0 ≠ 0 → K0.relIndex K ≠ 0 → K.relIndex K0 ≠ 0 →
    _root_.GlobalTheory.HL.invVol K0 K = _root_.GlobalTheory.HL.invVol K0 K1 * _root_.GlobalTheory.HL.invVol K1 K ∧
    0 < _root_.GlobalTheory.HL.invVol K0 K ∧
    (K ≤ K1 → _root_.GlobalTheory.HL.invVol K0 K =
      _root_.GlobalTheory.HL.invVol K0 K1 * (K.relIndex K1 : ℝ)) ∧
    ∀ g : G, _root_.GlobalTheory.HL.invVol (MulAut.conj g • K0) (MulAut.conj g • K) =
      _root_.GlobalTheory.HL.invVol K0 K := by
  intro G _ K0 K1 K h01 h10 h0K hK0
  have hd0 : (K0 ⊓ K1 ⊓ K).relIndex K0 ≠ 0 :=
    Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero (by simp) h10) hK0
  have hd1 : (K0 ⊓ K1 ⊓ K).relIndex K1 ≠ 0 := Subgroup.relIndex_ne_zero_trans hd0 h01
  have hdK : (K0 ⊓ K1 ⊓ K).relIndex K ≠ 0 := Subgroup.relIndex_ne_zero_trans hd0 h0K
  have l0 : K0 ⊓ K1 ⊓ K ≤ K0 := inf_le_left.trans inf_le_left
  have l1 : K0 ⊓ K1 ⊓ K ≤ K1 := inf_le_left.trans inf_le_right
  have lK : K0 ⊓ K1 ⊓ K ≤ K := inf_le_right
  have e0K := _root_.GlobalTheory.HL.invVol_eq_div_of_le l0 lK hd0
  have e01 := _root_.GlobalTheory.HL.invVol_eq_div_of_le l0 l1 hd0
  have e1K := _root_.GlobalTheory.HL.invVol_eq_div_of_le l1 lK hd1
  have hmul : _root_.GlobalTheory.HL.invVol K0 K =
      _root_.GlobalTheory.HL.invVol K0 K1 * _root_.GlobalTheory.HL.invVol K1 K := by
    rw [e0K, e01, e1K, div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr hd1)]
  refine ⟨hmul, ?_, ?_, ?_⟩
  · rw [e0K]
    exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdK))
  · intro hle
    have h1 : K1.relIndex K = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [hmul]
    congr 1
    unfold _root_.GlobalTheory.HL.invVol
    rw [h1, Nat.cast_one, div_one]
  · intro g
    have hc : ∀ L : Subgroup G, MulAut.conj g • L = ConjAct.toConjAct g • L := fun L => rfl
    unfold _root_.GlobalTheory.HL.invVol
    rw [hc, hc, Subgroup.relIndex_pointwise_smul, Subgroup.relIndex_pointwise_smul]

end GlobalTheory.HL
