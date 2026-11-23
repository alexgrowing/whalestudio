import Formalism.YangianSpanCharacter.StatementF
import Formalism.YangianSpanCharacter.YangianRTTProofs.SymplecticTransposeEntryZeroOne
import Formalism.YangianSpanCharacter.YangianRTTProofs.DiagonalEntryEqOfModularRelation

namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.YangianSpanCharacter.F

set_option linter.unusedSimpArgs false

theorem plus_frame_identity : Formalism.YangianSpanCharacter.F.PlusFrame := by
  intro 𝕜 A _ _ _ t τinv q S H Y Ya hY hYa hD hD1 D tn l M N G Ginv
  have hD' : D ≠ 0 := hD
  have hne : Y ≠ Ya := sub_ne_zero.mp hD
  have hτl : t Y 1 1 * l = t Y 1 0 := by
    show t Y 1 1 * (τinv Y * t Y 1 0) = t Y 1 0
    rw [← mul_assoc, (H.2.2.2.1 Y hY).1, one_mul]
  have hη : D • eta t τinv Y Ya = l - lf t τinv Ya := by
    unfold eta; exact smul_inv_smul₀ hD _
  have Y1 : t Y 1 1 * lf t τinv Ya - lf t τinv Ya * t Y 1 1 = -(t Y 1 1 * eta t τinv Y Ya) :=
    commutator_of_modular_relation H hY hYa hne
  have Y2 : l * lf t τinv Ya - lf t τinv Ya * l = eta t τinv Y Ya * l - eta t τinv Y Ya * lf t τinv Ya :=
    by rw [commutator_eq_eta_mul_sub H hY hYa hne, mul_sub]
  have hτη : D • (t Y 1 1 * eta t τinv Y Ya) = t Y 1 1 * l - t Y 1 1 * lf t τinv Ya := by
    rw [← mul_smul_comm, hη, mul_sub]
  have f1 : D • (l * eta t τinv Y Ya) = l * l - l * lf t τinv Ya := by
    rw [← mul_smul_comm, hη, mul_sub]
  have f2 : D • (lf t τinv Ya * eta t τinv Y Ya) = lf t τinv Ya * l - lf t τinv Ya * lf t τinv Ya := by
    rw [← mul_smul_comm, hη, mul_sub]
  have f3 : D • (eta t τinv Y Ya * l) = l * l - lf t τinv Ya * l := by
    rw [← smul_mul_assoc, hη, sub_mul]
  have f4 : D • (eta t τinv Y Ya * lf t τinv Ya) = l * lf t τinv Ya - lf t τinv Ya * lf t τinv Ya := by
    rw [← smul_mul_assoc, hη, sub_mul]
  have hDD : D * D⁻¹ = 1 := mul_inv_cancel₀ hD'
  have hηe : eta t τinv Y Ya = D⁻¹ • (l - lf t τinv Ya) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, M, blk, sc, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg, hτl]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, N, blk, sc, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg, hτl]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;> simp [G, Ginv]
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [G, M, sc, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) (-D) • Y1 + hτη
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [N, M, Ginv, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    · linear_combination (norm := module) hη
    · rw [smul_smul, inv_mul_cancel₀ hD', one_smul]
    · apply smul_cancel hD'
      linear_combination (norm := module) (-1 : 𝕜) • f1 - (D - 1) • f2 - ((D - 1) * D) • Y2 -
        (D - 1) • f3 + (D - 1) • f4
    · rw [hηe]
      linear_combination (norm := module) -(hDD • l)

theorem minus_frame_identity : Formalism.YangianSpanCharacter.F.MinusFrame := by
  intro 𝕜 A _ _ _ t τinv q S H Y Yb hY hY1 hYb hYb1 hYbm hd hd1 d tn τn Ln Gb
  have hd1' : d - 1 ≠ 0 := hd1
  have hne : Y ≠ Yb := fun h => hd (by rw [h, sub_self])
  have i0 := H.2.2.2.1 Y hY
  have hτl : t Y 1 1 * lf t τinv Y = t Y 1 0 := by
    unfold lf; rw [← mul_assoc, i0.1, one_mul]
  have hτm : t Y 1 1 * mf t τinv Y = t Y 0 1 := by
    unfold mf; rw [← mul_assoc, i0.1, one_mul]
  have QD : t Y 0 0 - t Y 0 1 * lf t τinv Y = q Y • τinv (Y + 1) := by
    have := qdet_mod H hY hY1; unfold lf; rw [← mul_assoc]; exact this
  have hτh : t Y 1 1 * hf τinv q Y = q Y • τinv (Y + 1) := by
    unfold hf; rw [mul_smul_comm, ← mul_assoc, i0.1, one_mul]
  have Y1' : t Y 1 1 * mf t τinv Yb - mf t τinv Yb * t Y 1 1 = t Y 1 1 * mu t τinv Y Yb :=
    y1'_mod H hY hYb hne
  have hμ0 : (Y - Yb) • mu t τinv Y Yb = mf t τinv Y - mf t τinv Yb := by
    unfold mu; exact smul_inv_smul₀ (sub_ne_zero.mpr hne) _
  have hτμ : d • (t Y 1 1 * mu t τinv Y Yb) = t Y 1 1 * mf t τinv Yb - t Y 0 1 := by
    show (Yb - Y) • (t Y 1 1 * mu t τinv Y Yb) = _
    rw [show Yb - Y = -(Y - Yb) by ring, neg_smul, ← mul_smul_comm, hμ0, mul_sub, hτm, neg_sub]
  have Y3 : (d - 1) • (mf t τinv Yb * lf t τinv Y - lf t τinv Y * mf t τinv Yb) =
      hf τinv q Y - hf τinv q (Yb - 1) :=
    yangian_relation_three_holds 𝕜 A t τinv q S H Yb Y hYb hYb1 hYbm hY hY1 (Ne.symm hne)
  have Y3' : mf t τinv Yb * lf t τinv Y - lf t τinv Y * mf t τinv Yb =
      (d - 1)⁻¹ • (hf τinv q Y - hf τinv q (Yb - 1)) := by
    rw [← Y3, inv_smul_smul₀ hd1']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, τn, blk, pt1, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [tn, blk, pt1, E1, Pf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    all_goals module
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [τn, Ln, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg, hτl]
    rw [inv_smul_smul₀ hd1', hτh]
    linear_combination (norm := module) QD
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [τn, Gb, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) (-d) • Y1' - hτμ
  · ext k l'
    fin_cases k <;> fin_cases l' <;>
      simp [Ln, Gb, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg]
    linear_combination (norm := module) Y3'

end Formalism.YangianSpanCharacter.P
