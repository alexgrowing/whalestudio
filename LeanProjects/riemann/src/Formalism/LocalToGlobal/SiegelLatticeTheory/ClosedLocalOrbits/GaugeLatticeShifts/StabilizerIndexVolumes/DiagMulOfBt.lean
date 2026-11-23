import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StClosed

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

section Tri

variable {K : Type*} [Field K] {N : ℕ}

theorem diag_mul_of_bt {α : Type*} [LinearOrder α] {b : Fin N → α} (hb : Function.Injective b)
    {A B : Matrix (Fin N) (Fin N) K} (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (i : Fin N) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne (hb.ne hk) with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem uni_inv {α : Type*} [LinearOrder α] {b : Fin N → α} (hb : Function.Injective b)
    {M : Matrix (Fin N) (Fin N) K} (hM : M.BlockTriangular b) (hd : ∀ i, M i i = 1)
    (hdet : IsUnit M.det) : M⁻¹.BlockTriangular b ∧ ∀ i, M⁻¹ i i = 1 := by
  haveI := M.invertibleOfIsUnitDet hdet
  have hI : M⁻¹.BlockTriangular b := Matrix.blockTriangular_inv_of_blockTriangular hM
  refine ⟨hI, fun i => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv M hdet) i) i
  rw [diag_mul_of_bt hb hM hI, hd, one_mul, Matrix.one_apply_eq] at h1
  exact h1

theorem lo_bt {L : Matrix (Fin N) (Fin N) K} (h : Formalism.MainNotions.S.IsLoUni L) :
    L.BlockTriangular OrderDual.toDual := by
  intro i j hij
  exact (h i j).1 (OrderDual.toDual_lt_toDual.mp hij)

theorem up_bt {U : Matrix (Fin N) (Fin N) K} (h : Formalism.MainNotions.S.IsUpUni U) : U.BlockTriangular id := by
  intro i j hij
  exact (h i j).1 hij

theorem lo_of {L : Matrix (Fin N) (Fin N) K} (h : L.BlockTriangular OrderDual.toDual)
    (hd : ∀ i, L i i = 1) : Formalism.MainNotions.S.IsLoUni L := by
  intro i j
  refine ⟨fun hij => h (OrderDual.toDual_lt_toDual.mpr hij), ?_⟩
  rintro rfl
  exact hd i

theorem up_of {U : Matrix (Fin N) (Fin N) K} (h : U.BlockTriangular id)
    (hd : ∀ i, U i i = 1) : Formalism.MainNotions.S.IsUpUni U := by
  intro i j
  refine ⟨fun hij => h hij, ?_⟩
  rintro rfl
  exact hd i

theorem lo_det {L : Matrix (Fin N) (Fin N) K} (h : Formalism.MainNotions.S.IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular (M := L) (lo_bt h)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem up_det {U : Matrix (Fin N) (Fin N) K} (h : Formalism.MainNotions.S.IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (M := U) (up_bt h)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem lo_mul {A B : Matrix (Fin N) (Fin N) K} (hA : Formalism.MainNotions.S.IsLoUni A) (hB : Formalism.MainNotions.S.IsLoUni B) :
    Formalism.MainNotions.S.IsLoUni (A * B) := by
  refine lo_of ((lo_bt hA).mul (lo_bt hB)) fun i => ?_
  rw [diag_mul_of_bt OrderDual.toDual.injective (lo_bt hA) (lo_bt hB), (hA i i).2 rfl, (hB i i).2 rfl, one_mul]

theorem up_mul {A B : Matrix (Fin N) (Fin N) K} (hA : Formalism.MainNotions.S.IsUpUni A) (hB : Formalism.MainNotions.S.IsUpUni B) :
    Formalism.MainNotions.S.IsUpUni (A * B) := by
  refine up_of ((up_bt hA).mul (up_bt hB)) fun i => ?_
  rw [diag_mul_of_bt Function.injective_id (up_bt hA) (up_bt hB), (hA i i).2 rfl, (hB i i).2 rfl, one_mul]

theorem lo_inv {A : Matrix (Fin N) (Fin N) K} (hA : Formalism.MainNotions.S.IsLoUni A) : Formalism.MainNotions.S.IsLoUni A⁻¹ := by
  obtain ⟨h1, h2⟩ := uni_inv OrderDual.toDual.injective (lo_bt hA) (fun i => (hA i i).2 rfl)
    (by rw [lo_det hA]; exact isUnit_one)
  exact lo_of h1 h2

theorem up_inv {A : Matrix (Fin N) (Fin N) K} (hA : Formalism.MainNotions.S.IsUpUni A) : Formalism.MainNotions.S.IsUpUni A⁻¹ := by
  obtain ⟨h1, h2⟩ := uni_inv Function.injective_id (up_bt hA) (fun i => (hA i i).2 rfl)
    (by rw [up_det hA]; exact isUnit_one)
  exact up_of h1 h2

theorem lo_one : Formalism.MainNotions.S.IsLoUni (1 : Matrix (Fin N) (Fin N) K) := by
  intro i j
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), ?_⟩
  rintro rfl
  exact Matrix.one_apply_eq i

theorem up_one : Formalism.MainNotions.S.IsUpUni (1 : Matrix (Fin N) (Fin N) K) := by
  intro i j
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), ?_⟩
  rintro rfl
  exact Matrix.one_apply_eq i

end Tri

theorem stClosed : StClosed := by
  unfold StClosed
  intro E _ _ n W
  simp only [StSet, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by rw [Units.val_one]; exact lo_one, 1, up_one, ?_⟩
    rw [Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · rintro a ⟨ha, b, hb, hab⟩ a' ⟨ha', b', hb', hab'⟩
    refine ⟨?_, b' * b, up_mul hb' hb, ?_⟩
    · rw [Units.val_mul]
      exact lo_mul ha ha'
    · rw [Units.val_mul]
      calc _ = (a : Matrix (Fin n) (Fin n) E) * ((a' : Matrix (Fin n) (Fin n) E) * W * b') * b := by
            simp only [Matrix.mul_assoc]
        _ = W := by rw [hab', hab]
  · rintro a ⟨ha, b, hb, hab⟩
    have hbdet : IsUnit b.det := by rw [up_det hb]; exact isUnit_one
    refine ⟨?_, b⁻¹, up_inv hb, ?_⟩
    · rw [Matrix.coe_units_inv]
      exact lo_inv ha
    · calc _ = ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) *
            ((a : Matrix (Fin n) (Fin n) E) * W * b) * b⁻¹ := by rw [hab]
        _ = (((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) *
            (a : Matrix (Fin n) (Fin n) E)) * W * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
        _ = W := by rw [Units.inv_mul, Matrix.mul_nonsing_inv b hbdet, Matrix.one_mul, Matrix.mul_one]

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
