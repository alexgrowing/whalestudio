import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

theorem continuous_matrix_inv_of_isUnit_det {T n : Type} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    {M : T → Matrix n n ℂ} (hM : Continuous M) (h : ∀ t, IsUnit (M t).det) : Continuous fun t => (M t)⁻¹ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hM.matrix_det.inv₀ fun t => (h t).ne_zero).smul hM.matrix_adjugate

theorem continuous_ker_right (P Q : ℕ) (T : Type) [TopologicalSpace T] (Y : Matrix (Ix P Q) (Fin Q) ℂ)
    (v φ : Ix P Q → ℂ) (Y' : T → Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : T → Ix P Q → ℂ) (hY : Continuous Y')
    (hv : Continuous v') (hφ : Continuous φ') (h : ∀ t, IsUnit (Yᴴ * Jm P Q * Y' t).det) :
    Continuous fun t => ker Y v φ (Y' t) (v' t) (φ' t) := by
  have hM : Continuous fun t => Yᴴ * Jm P Q * Y' t := continuous_const.matrix_mul hY
  have hI := continuous_matrix_inv_of_isUnit_det hM h
  unfold ker
  refine (hM.neg.matrix_det.inv₀ fun t => ?_).mul (Complex.continuous_exp.comp (Continuous.sub
    (continuous_const.dotProduct hv) ((continuous_const.add hφ).dotProduct
      ((((hY.matrix_mul hI).matrix_mul continuous_const).matrix_mul continuous_const).matrix_mulVec
        (continuous_const.add hv)))))
  rw [Pi.neg_apply, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (h t).ne_zero

end GlobalTheory.OscGauss
