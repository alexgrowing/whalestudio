import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

theorem LinesQuotIndexLog.proof (h1 : LinesQuotIndexSplit.Statement)
    (h2 : LinesProjIndexLower.Statement) (h3 : LinesIdealIndexPos.Statement)
    (h4 : LinesProductFormula.Statement) (h5 : LinesCoordDet.Statement) :
    LinesQuotIndexLog.Statement := by
  intro K _ _ n m k a B b c τ ha hBl hBr hτ hli
  have hsplit := h1 K n m k a B b c τ ha hBl hBr hτ hli
  have hlow := h2 K n m k a B τ ha hBr hτ
  have hpos : 0 < ∏ j, idealIndex (a (τ j)) :=
    Finset.prod_pos fun j _ => h3 K (a (τ j)) (ha (τ j))
  have hdet := (h5 K n m k B b c hBl hli).2
  have hN : Algebra.norm ℚ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hdet
  have hpf := h4 K _ hdet
  have hGpos := lt_of_lt_of_le hpos hlow
  have hNabs : |((Algebra.norm ℚ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det : ℚ) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hN)
  rw [hsplit, Real.log_mul hGpos.ne' hNabs, hpf,
    ← Real.log_prod fun j _ => (h3 K (a (τ j)) (ha (τ j))).ne']
  exact add_le_add (Real.log_le_log hpos hlow) le_rfl

end GroundTheory.Heights₂.Heights
