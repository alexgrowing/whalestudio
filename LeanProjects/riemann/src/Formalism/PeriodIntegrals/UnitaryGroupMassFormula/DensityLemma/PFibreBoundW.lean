import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundV

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

namespace NBk

variable {k r : ℕ}

lemma mul_diagonal_conjTranspose_apply (P Q : Matrix (Fin r) (Fin (k + 1)) ℂ) (a b : Fin r) :
    (P * Matrix.diagonal (hW k) * Qᴴ) a b = ∑ j, P a j * hW k j * star (Q b j) := by
  rw [Matrix.mul_apply]; simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

lemma nbm_cm (Ba B : Matrix (Fin r) (Fin (k + 1)) ℂ) (Sa S : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    cmOf k r (Ba + B) (Sa + S + (1 / 2 : ℂ) •
        (B * Matrix.diagonal (hW k) * Baᴴ - Ba * Matrix.diagonal (hW k) * Bᴴ)) a b =
      cmOf k r B S a b + -(Ba * Matrix.diagonal (hW k) * Bᴴ) a b + cmOf k r Ba Sa a b := by
  unfold cmOf
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem nbm_mul (Ba B : Matrix (Fin r) (Fin (k + 1)) ℂ) (Sa S : Matrix (Fin r) (Fin r) ℂ) :
    unipotentBlockMatrix k r Ba Sa * unipotentBlockMatrix k r B S =
      unipotentBlockMatrix k r (Ba + B) (Sa + S + (1 / 2 : ℂ) •
        (B * Matrix.diagonal (hW k) * Baᴴ - Ba * Matrix.diagonal (hW k) * Bᴴ)) := by
  ext p q
  rw [Matrix.mul_apply, sum_split]
  induction p using cases3 <;> induction q using cases3 <;>
    simp only [nb_ee, nb_we, nb_se, nb_ew, nb_ww, nb_sw, nb_es, nb_ws, nb_ss, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, ite_mul, mul_ite, one_mul, mul_one, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.add_apply, star_add]
  all_goals first
    | done
    | (rw [nbm_cm, mul_diagonal_conjTranspose_apply, ← Finset.sum_neg_distrib]; ring)
    | ring

end NBk

end PI.UnitaryGroupMassFormula.DLm
