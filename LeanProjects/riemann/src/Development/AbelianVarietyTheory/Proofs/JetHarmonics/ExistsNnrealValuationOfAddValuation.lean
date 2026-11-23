import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration

namespace GlobalTheory

open scoped NNReal

noncomputable def expNegTop : WithTop ℚ → ℝ≥0
  | ⊤ => 0
  | (q : ℚ) => ⟨Real.exp (-(q : ℝ)), (Real.exp_pos _).le⟩

@[simp] theorem expNegTop_top : expNegTop ⊤ = 0 := rfl

theorem expNegTop_coe (q : ℚ) : ((expNegTop (q : WithTop ℚ) : ℝ≥0) : ℝ) = Real.exp (-(q : ℝ)) := rfl

theorem expNegTop_zero : expNegTop 0 = 1 := by
  apply NNReal.coe_injective
  have h := expNegTop_coe 0
  simpa using h

theorem expNegTop_add (a b : WithTop ℚ) : expNegTop (a + b) = expNegTop a * expNegTop b := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      apply NNReal.coe_injective
      rw [← WithTop.coe_add, NNReal.coe_mul, expNegTop_coe, expNegTop_coe, expNegTop_coe,
        ← Real.exp_add]
      push_cast
      ring_nf

theorem expNegTop_le_iff (a b : WithTop ℚ) : expNegTop a ≤ expNegTop b ↔ b ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top =>
      rw [← NNReal.coe_le_coe, expNegTop_coe]
      simp only [expNegTop_top, NNReal.coe_zero, top_le_iff, WithTop.coe_ne_top, iff_false, not_le]
      exact Real.exp_pos _
    | coe b =>
      rw [← NNReal.coe_le_coe, expNegTop_coe, expNegTop_coe, Real.exp_le_exp, neg_le_neg_iff,
        Rat.cast_le, WithTop.coe_le_coe]

noncomputable def expNegValuation {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    Valuation F ℝ≥0 where
  toFun x := expNegTop (v x)
  map_zero' := by simp
  map_one' := by simp [expNegTop_zero]
  map_mul' x y := by rw [v.map_mul, expNegTop_add]
  map_add_le_max' x y := by
    rcases min_le_iff.mp (v.map_add x y) with h | h
    · exact le_max_of_le_left ((expNegTop_le_iff _ _).mpr h)
    · exact le_max_of_le_right ((expNegTop_le_iff _ _).mpr h)

theorem expNegValuation_apply {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x = expNegTop (v x) := rfl

theorem expNegValuation_le_one_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x ≤ 1 ↔ 0 ≤ v x := by
  rw [expNegValuation_apply, ← expNegTop_zero, expNegTop_le_iff]

theorem exists_nnreal_valuation_of_addValuation :
    ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)), ∃ v' : Valuation F NNReal,
      (∀ x y, v' x ≤ v' y ↔ v y ≤ v x) ∧ v'.Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  intro F _ v
  refine ⟨expNegValuation v, fun x y => expNegTop_le_iff _ _, ?_, ?_, ?_⟩
  · exact Subtype.val_injective
  · intro x
    exact (expNegValuation_le_one_iff v _).mpr x.2
  · intro r hr
    exact ⟨⟨r, (expNegValuation_le_one_iff v r).mp hr⟩, rfl⟩

end GlobalTheory
