import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stairElt_diag (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (e : ℕ) (J : G.Level) (X : ℕ × ℕ) :
    ∃ n : Fin (G.rank X) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X =
        diagGL fun a => ϖ ^ n a := by
  have h1 : ∀ Y : ℕ × ℕ, ∃ n : Fin (G.rank Y) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (1 : GL (Fin (G.rank Y)) k) = diagGL fun a => ϖ ^ n a := fun Y =>
    ⟨fun _ => 0, fun _ => Nat.zero_le _, Units.ext (by simp)⟩
  have h2 : ∀ j : ℕ, ∃ n : Fin (G.rank (G.m, j)) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      stair G ϖ e j = diagGL fun a => ϖ ^ n a := fun j =>
    ⟨fun a => e * (a.val + 1 - topRank G j), fun a => Nat.mul_le_mul_left _ (by
      have := topRank_add hs j; have := a.2; omega), rfl⟩
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]; exact h2 j
    · rw [Reps.elt, onColumn_apply]
      cases j with
      | zero => exact h2 0
      | succ j =>
        have : ¬ j < G.m - 2 := by omega
        simp only [dif_neg this]
        exact h1 _
  · rw [Reps.elt, onColumn, dif_neg hi]
    exact h1 _

theorem valuation_fill_sub_le (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (n : ℕ) (x : ColArgs G) (y : RowArgs G)
    (v l : Vars G) (hl : l ∈ varLat G ϖ n) (b : Edge) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    valuation k ((fill hs x y (v + l) - fill hs x y v) b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ <;> simp only [Pi.sub_apply, Matrix.sub_apply, fill] <;> split_ifs
  · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, downMap]
    split_ifs with h
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, stepPt, Matrix.add_apply, Matrix.of_apply,
        add_sub_add_left_eq_sub]
      split_ifs
      · simp only [Pi.add_apply, add_sub_cancel_left]
        exact hl ⟨j, h⟩ _
      · simp
    · simp
    · simp
  all_goals simp

end

theorem moved_stair_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s)
    (ϖ : kˣ), IsUnif ϖ → ∀ (e : ℕ) (T : G.Args → ℂ), G.IsTensor ϖ e (oppositePath G.m) T → ∀ (J : G.Level) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (v l : Vars G), l ∈ varLat G ϖ (G.m * e) →
    moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y (v + l)) =
      moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y v) := by
  intro k _ _ _ _ G hs ϖ hϖ e T hT J keep x y v l hl
  rcases Nat.eq_zero_or_pos G.m with hm | hm
  · have : l = 0 := funext fun j => absurd j.2 (by omega)
    rw [this, add_zero]
  have hd := stairElt_diag G hs ϖ e J
  generalize (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) = g at hd ⊢
  have hf := valuation_fill_sub_le G hs ϖ _ x y v l hl
  have hsum : G.moveArgs .one g (fill hs x y (v + l)) =
      G.moveArgs .one g (fill hs x y v) + G.moveArgs .one g (fill hs x y (v + l) - fill hs x y v) := by
    funext b
    simp only [Grid.moveArgs, Pi.add_apply, Pi.sub_apply, Matrix.mul_sub, Matrix.sub_mul, add_sub_cancel]
  simp only [moved, Grid.pathAct]
  rw [hsum, hT.2.2]
  intro b r
  generalize fill hs x y (v + l) - fill hs x y v = d at hf
  obtain ⟨n, -, hn⟩ := hd b.tgt
  obtain ⟨n', hn1, hn'⟩ := hd b.src
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  rw [SplitFlip.stdLat, smul_diagLat, mem_diagLat]
  intro s
  have hv : (G.moveArgs .one g d b).row r s = (ϖ : k) ^ n r * d b r s * ((ϖ : k) ^ n' s)⁻¹ := by
    have hinv : ((diagGL fun a => ϖ ^ n' a : GL (Fin (G.rank b.src)) k)⁻¹).val =
        Matrix.diagonal fun a => ((ϖ : k) ^ n' a)⁻¹ := by
      rw [Matrix.coe_units_inv]
      refine Matrix.inv_eq_right_inv ?_
      simp [Matrix.diagonal_mul_diagonal]
    simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val, hn, hn', hinv, diagGL_val,
      Matrix.diagonal_transpose, Matrix.row, Matrix.mul_diagonal, Matrix.diagonal_mul, Units.val_pow_eq_pow_val]
  have h2 := hf b r s
  rw [hv]
  simp only [map_mul, map_inv₀, map_pow, Units.val_pow_eq_pow_val, Pi.one_apply, mul_one] at h2 ⊢
  rw [mul_inv_le_iff₀ (pow_pos h0 _), ← pow_add]
  refine (mul_le_of_le_one_left' (pow_le_one' h1 _)).trans (h2.trans (pow_le_pow_right_of_le_one' h1 ?_))
  have := hn1 s
  obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le' hm
  rw [hm'] at this ⊢
  simp only [Nat.succ_eq_add_one, zero_add, Nat.add_sub_cancel] at this ⊢
  nlinarith

end GlobalTheory.UnfoldLoss
