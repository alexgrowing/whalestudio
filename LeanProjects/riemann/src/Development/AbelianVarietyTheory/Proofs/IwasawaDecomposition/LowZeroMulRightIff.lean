import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Datum
open scoped Matrix

namespace GlobalTheory.TwistDatumRight

section
variable {κ : Type} [CommRing κ] {b r : ℕ}

theorem topL_mul_right (y : Matrix (Fin b) (Fin r) κ) (h : Matrix (Fin r) (Fin r) κ) :
    topL r (y * h) = topL r y * h := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, hi, Matrix.mul_apply]
  · simp [topL, hi, Matrix.mul_apply]

theorem lowZero_mul_right {y : Matrix (Fin b) (Fin r) κ} (hy : LowZero r y) (h : Matrix (Fin r) (Fin r) κ) :
    LowZero r (y * h) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => by rw [hy i k hi k.2, zero_mul]

theorem lowZero_mul_right_iff (y : Matrix (Fin b) (Fin r) κ) (h : GL (Fin r) κ) :
    LowZero r (y * h.1) ↔ LowZero r y := by
  refine ⟨fun H => ?_, fun H => lowZero_mul_right H _⟩
  have := lowZero_mul_right H (h⁻¹).1
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this

theorem det_topL_mul_right (y : Matrix (Fin b) (Fin r) κ) (h : GL (Fin r) κ) :
    (topL r (y * h.1)).det = ((Matrix.GeneralLinearGroup.det h : κˣ) : κ) * (topL r y).det := by
  rw [topL_mul_right, Matrix.det_mul, mul_comm, Matrix.GeneralLinearGroup.val_det_apply]

end

theorem omegaQ_mul_right : ∀ (D : D7) (b r : ℕ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (h : ∀ PP : Pl D.host.E, GL (Fin r) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin r) (kP PP)), (∀ PP ∈ Q, y' PP = y PP * (h PP).1) → omegaQ Q r ξ (-1) y' = ((∏ PP ∈ Q, ξ PP (Matrix.GeneralLinearGroup.det (h PP)) : ℂˣ) : ℂ)⁻¹ * omegaQ Q r ξ (-1) y := by
  intro D b r Q ξ h y y' hy
  have hiff : (∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det) ↔
      (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) := by
    refine forall₂_congr fun PP hP => ?_
    rw [hy PP hP, lowZero_mul_right_iff, det_topL_mul_right, Units.isUnit_units_mul]
  unfold omegaQ
  by_cases c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dif_pos c, dif_pos (hiff.2 c), ← Finset.prod_attach Q, Units.coe_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : ((hiff.2 c) PP.1 PP.2).2.unit =
        Matrix.GeneralLinearGroup.det (h PP.1) * (c PP.1 PP.2).2.unit := by
      apply Units.ext
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hy PP.1 PP.2, det_topL_mul_right]
    rw [e, map_mul, Units.val_mul, zpow_neg_one, zpow_neg_one, mul_inv]
  · rw [dif_neg c, dif_neg (fun h' => c (hiff.1 h')), mul_zero]

end GlobalTheory.TwistDatumRight
