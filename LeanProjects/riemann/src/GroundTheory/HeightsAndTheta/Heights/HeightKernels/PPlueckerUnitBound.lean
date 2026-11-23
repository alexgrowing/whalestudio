import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset
open scoped ComplexOrder

namespace PlueckerUnitBoundAlt

theorem posSemidef_one_add {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    (1 + Z * Zᴴ).PosSemidef :=
  Matrix.PosSemidef.one.add (Matrix.posSemidef_self_mul_conjTranspose Z)

theorem diag_eq {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, ‖Z a b‖ = 1) (a : Fin j) :
    (1 + Z * Zᴴ : Matrix (Fin j) (Fin j) ℂ) a a = (((1 + m : ℝ)) : ℂ) := by
  have hb : ∀ b, Z a b * Zᴴ b a = 1 := by
    intro b
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      hZ a b]
    norm_num
  rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply]
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

end PlueckerUnitBoundAlt

open PlueckerUnitBoundAlt in

theorem PlueckerUnitBound.proof (h : HadamardPSD.Statement) : PlueckerUnitBound.Statement := by
  intro j m Z hZ
  calc ‖(1 + Z * Zᴴ).det‖ ≤ ∏ a, ‖(1 + Z * Zᴴ : Matrix (Fin j) (Fin j) ℂ) a a‖ := h j _ (posSemidef_one_add Z)
    _ = ∏ _a : Fin j, (1 + m : ℝ) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [diag_eq Z hZ a, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ = (1 + m : ℝ) ^ j := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GroundTheory.Heights₂.Heights
