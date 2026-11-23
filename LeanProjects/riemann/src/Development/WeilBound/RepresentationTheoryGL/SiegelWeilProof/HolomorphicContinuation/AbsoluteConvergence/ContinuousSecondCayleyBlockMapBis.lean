import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BanachHol

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_group_lower_left_block : Continuous (fun g : GR n => (mR g).toBlocks₂₁) := by
  exact continuous_mR.matrix_submatrix Sum.inr Sum.inl

theorem continuous_group_lower_right_block : Continuous (fun g : GR n => (mR g).toBlocks₂₂) := by
  exact continuous_mR.matrix_submatrix Sum.inr Sum.inr

theorem continuous_first_cayley_block_map : Continuous (fun g : GR n => u1 (mR g)) := by
  unfold u1
  exact ((continuous_group_lower_left_block (n := n)).const_smul Complex.I).add continuous_group_lower_right_block

theorem continuous_second_cayley_block_map : Continuous (fun g : GR n => u2 (mR g)) := by
  unfold u2
  exact ((continuous_group_lower_left_block (n := n)).const_smul Complex.I).neg.add continuous_group_lower_right_block

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hdet : Continuous (fun g : GR n => (mR g).det) := continuous_mR.matrix_det
  have h1 : Continuous (fun g : GR n => (u1 (mR g)).det) := continuous_first_cayley_block_map.matrix_det
  have h2 : Continuous (fun g : GR n => (u2 (mR g)).det) := continuous_second_cayley_block_map.matrix_det
  have hne : ∀ g : GR n, (mR g).det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g : GL (Fin n ⊕ Fin n) ℂ))).ne_zero
  show Continuous (fun g : GR n =>
    (mR g).det ^ e * ((u1 (mR g)).det ^ (-(p : ℤ)) * (u2 (mR g)).det ^ (-(q : ℤ))))
  exact (hdet.zpow₀ e fun g => Or.inl (hne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (hD n g).1).mul (h2.zpow₀ _ fun g => Or.inl (hD n g).2))

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  unfold hLoc
  exact ((continuous_first_cayley_block_map.matrix_det).norm.pow 2).inv₀ fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hD n g).1)

theorem hLoc_nonneg (g : GR n) : 0 ≤ hLoc g := by
  unfold hLoc
  positivity

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hD n g).1) 2)

theorem first_cayley_block_one : u1 (mR (1 : GR n)) = 1 := by
  ext i j
  simp [u1, mR, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem second_cayley_block_one : u2 (mR (1 : GR n)) = 1 := by
  ext i j
  simp [u2, mR, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 (n := n) p q e 1 = 1 := by
  simp only [F0, f0, first_cayley_block_one, second_cayley_block_one]
  simp [mR]

end PositivityTheory.Rg.Sw.AbsSt.Vac
