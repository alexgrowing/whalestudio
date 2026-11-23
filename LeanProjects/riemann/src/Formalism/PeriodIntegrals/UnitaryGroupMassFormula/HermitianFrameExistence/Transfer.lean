import Mathlib
import Formalism.PeriodIntegrals.ScPiExists

noncomputable section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

theorem hJ_rv (I : Formalism.MainNotions.S.AutInst) (v : NumberField.InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hstar : ∀ a : I.E, I.φ v (star a) = star (I.φ v a) := fun a =>
    I.cm.cmUnram.2.1 (I.φ v) a
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have key : hJ (I.ε v) (rv I v x) (rv I v y) =
      star (fun i => I.φ v (x i)) ⬝ᵥ ((I.J.map (I.φ v)) *ᵥ fun j => I.φ v (y j)) := by
    unfold hJ rv
    rw [← I.P_spec v, Matrix.mulVec_mulVec, Matrix.mul_assoc, hP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
      Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  rw [key]
  simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_apply, hstar, dotProduct, mulVec,
    Matrix.map_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]

end PI.ScPiFrameW
