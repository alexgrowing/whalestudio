import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset

noncomputable section

namespace PlueckerNormSqAlt

theorem onePipe_mul_conjTranspose {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    onePipe Z * (onePipe Z)ᴴ = 1 + Z * Zᴴ := by
  ext a b
  simp only [mul_apply, conjTranspose_apply, onePipe, of_apply, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Matrix.add_apply]
  congr 1
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem rowsOf_conjTranspose {j N : ℕ} (A : Matrix (Fin j) (Fin N) ℂ)
    (I : {I : Finset (Fin N) // I.card = j}) : rowsOf Aᴴ I = (colsOf A I)ᴴ := by
  ext a b
  simp [rowsOf, colsOf, conjTranspose_apply]

end PlueckerNormSqAlt

open PlueckerNormSqAlt in

theorem PlueckerNormSq.proof (h : CauchyBinet.Statement) : PlueckerNormSq.Statement := by
  intro j m Z
  rw [← onePipe_mul_conjTranspose, h ℂ j (j + m) (onePipe Z) (onePipe Z)ᴴ]
  push_cast
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [rowsOf_conjTranspose, det_conjTranspose, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  rfl

end

end GroundTheory.Heights₂.Heights
