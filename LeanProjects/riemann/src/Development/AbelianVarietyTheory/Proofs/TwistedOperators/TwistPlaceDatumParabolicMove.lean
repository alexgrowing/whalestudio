import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParabolicDatum

section Ring

variable {κ : Type} [CommRing κ] {a b r : ℕ}

theorem tri_zero {n : ℕ} {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) (i j : Fin n) (hi : r ≤ i.val) (hj : j.val < r) :
    g.val i j = 0 := by
  rw [Formalism.L2.DIV.mem_blockTri] at hg
  apply hg
  simp only [Formalism.L2.DIV.blk2, if_pos hj, if_neg (not_lt.mpr hi)]
  exact Nat.zero_lt_one

theorem lowZero_mul {c : ℕ} {x : Matrix (Fin c) (Fin b) κ} {y : Matrix (Fin b) (Fin a) κ}
    (hx : LowZero r x) (hy : LowZero r y) : LowZero r (x * y) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < r
  · rw [hx i l hi hl, zero_mul]
  · rw [hy l j (not_lt.mp hl) hj, mul_zero]

theorem lowZero_of_tri {n : ℕ} {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) : LowZero r g.val := fun i j hi hj => tri_zero hg i j hi hj

theorem topL_eq (ha : r ≤ a) (hb : r ≤ b) (y : Matrix (Fin b) (Fin a) κ) :
    topL r y = y.submatrix (Fin.castLE hb) (Fin.castLE ha) := by
  ext i j
  have hij : i.val < b ∧ j.val < a := ⟨lt_of_lt_of_le i.isLt hb, lt_of_lt_of_le j.isLt ha⟩
  simp only [topL, dif_pos hij, Matrix.submatrix_apply]
  rfl

theorem topL_mul {c : ℕ} (ha : r ≤ a) (hb : r ≤ b) (hc : r ≤ c) (x : Matrix (Fin c) (Fin b) κ)
    {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) : topL r (x * y) = topL r x * topL r y := by
  rw [topL_eq ha hc, topL_eq hb hc, topL_eq ha hb]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hb) (Fin.castLE_injective hb) _ _ ?_ fun l => rfl
  intro l hl
  have hrl : r ≤ l.val := by
    by_contra hlt
    exact hl ⟨⟨l.val, not_le.mp hlt⟩, rfl⟩
  rw [hy l _ hrl (by simp), mul_zero]

theorem topL_tri {n : ℕ} (hn : r ≤ n) {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) :
    topL r g.val = (upperLeftBlock hn g).val := by
  rw [topL_eq hn hn, Formalism.L2.DIV.upper_block_val_submatrix hn hg]

theorem det_blockTriangular_eq_mul_diagBlocks {n : ℕ} (hn : r ≤ n) {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hn g) * dBlk (blk2 r) 1 g := by
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Formalism.L2.DIV.upper_block_val_submatrix hn hg, Formalism.L2.DIV.diag_block_det_val 1 hg,
    Matrix.twoBlockTriangular_det (g : Matrix (Fin n) (Fin n) κ) (fun i : Fin n => i.val < r)
      (fun i hi j hj => tri_zero hg i j (not_lt.mp hi) hj)]
  congr 1
  · let e : Fin r ≃ {i : Fin n // i.val < r} :=
      ⟨fun i => ⟨Fin.castLE hn i, i.isLt⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  · let e : {i : Fin n // Formalism.L2.DIV.blk2 r i = 1} ≃ {i : Fin n // ¬ i.val < r} :=
      Equiv.subtypeEquivRight fun i => by
        unfold Formalism.L2.DIV.blk2
        split_ifs with h <;> simp [h]
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl

theorem lowZero_move {G : GL (Fin a) κ} {H : GL (Fin b) κ} (hG : G ∈ blockTri (blk2 r)) (hH : H ∈ blockTri (blk2 r))
    (y : Matrix (Fin b) (Fin a) κ) : LowZero r ((H⁻¹).val * y * G.val) ↔ LowZero r y := by
  constructor
  · intro h
    have hy : y = H.val * ((H⁻¹).val * y * G.val) * (G⁻¹).val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        Units.mul_inv, Matrix.mul_one]
    rw [hy]
    exact lowZero_mul (lowZero_mul (lowZero_of_tri hH) h) (lowZero_of_tri (Subgroup.inv_mem _ hG))
  · intro h
    exact lowZero_mul (lowZero_mul (lowZero_of_tri (Subgroup.inv_mem _ hH)) h) (lowZero_of_tri hG)

theorem det_topL_move (ha : r ≤ a) (hb : r ≤ b) {G : GL (Fin a) κ} {H : GL (Fin b) κ} (hG : G ∈ blockTri (blk2 r))
    (hH : H ∈ blockTri (blk2 r)) {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) :
    (topL r ((H⁻¹).val * y * G.val)).det =
      ((Matrix.GeneralLinearGroup.det G * (dBlk (blk2 r) 1 G)⁻¹ *
        ((Matrix.GeneralLinearGroup.det H)⁻¹ * dBlk (blk2 r) 1 H) : κˣ) : κ) * (topL r y).det := by
  have hHi : H⁻¹ ∈ blockTri (blk2 r) := Subgroup.inv_mem _ hH
  have e1 : topL r ((H⁻¹).val * y * G.val) = (upperLeftBlock hb H⁻¹).val * topL r y * (upperLeftBlock ha G).val := by
    rw [topL_mul ha ha hb _ (lowZero_of_tri hG), topL_mul ha hb hb _ hy, topL_tri hb hHi, topL_tri ha hG]
  have key : (Matrix.GeneralLinearGroup.det G * (dBlk (blk2 r) 1 G)⁻¹ *
      ((Matrix.GeneralLinearGroup.det H)⁻¹ * dBlk (blk2 r) 1 H) : κˣ) =
      Matrix.GeneralLinearGroup.det (upperLeftBlock hb H⁻¹) * Matrix.GeneralLinearGroup.det (upperLeftBlock ha G) := by
    have dG := det_blockTriangular_eq_mul_diagBlocks ha hG
    have dH := det_blockTriangular_eq_mul_diagBlocks hb hHi
    have dinv : dBlk (blk2 r) 1 H⁻¹ = (dBlk (blk2 r) 1 H)⁻¹ :=
      Formalism.L2.DIV.extendOne_inv (Formalism.L2.DIV.blkDet (blk2 r) 1) hH
    rw [map_inv, dinv] at dH
    rw [dG, dH, mul_inv_cancel_right, inv_mul_cancel_right, mul_comm]
  rw [e1, Matrix.det_mul, Matrix.det_mul, key, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply]
  ring

end Ring

theorem omegaQ_parabolic : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (n : ℤ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Q, G PP ∈ blockTri (blk2 r) ∧ H PP ∈ blockTri (blk2 r)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaQ Q r ξ n (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Q, (ξ PP (Matrix.GeneralLinearGroup.det (G PP)) * (ξ PP (dBlk (blk2 r) 1 (G PP)))⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (H PP)))⁻¹ * ξ PP (dBlk (blk2 r) 1 (H PP)))) ^ n : ℂˣ) : ℂ) * omegaQ Q r ξ n y := by
  intro D a b r ha hb Q ξ n G H hGH y
  have hdet : ∀ PP ∈ Q, LowZero r (y PP) →
      (topL r (((H PP)⁻¹).val * y PP * (G PP).val)).det =
        ((Matrix.GeneralLinearGroup.det (G PP) * (dBlk (blk2 r) 1 (G PP))⁻¹ *
          ((Matrix.GeneralLinearGroup.det (H PP))⁻¹ * dBlk (blk2 r) 1 (H PP)) : (kP PP)ˣ) : kP PP) *
          (topL r (y PP)).det :=
    fun PP hP hy => det_topL_move ha hb (hGH PP hP).1 (hGH PP hP).2 hy
  have hcond : (∀ PP ∈ Q, LowZero r (((H PP)⁻¹).val * y PP * (G PP).val) ∧
      IsUnit (topL r (((H PP)⁻¹).val * y PP * (G PP).val)).det) ↔
      ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det := by
    refine forall₂_congr fun PP hP => ?_
    rw [lowZero_move (hGH PP hP).1 (hGH PP hP).2 (y PP)]
    refine and_congr_right fun hy => ?_
    rw [hdet PP hP hy]
    exact Units.isUnit_units_mul _ _
  unfold omegaQ
  split_ifs with h1 h2 h2
  · simp only [← Units.val_zpow_eq_zpow_val, ← Units.coe_prod, ← Units.val_mul]
    congr 1
    rw [← Finset.prod_attach Q, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [← mul_zpow]
    congr 1
    have hu : (h1 PP.1 PP.2).2.unit =
        (Matrix.GeneralLinearGroup.det (G PP.1) * (dBlk (blk2 r) 1 (G PP.1))⁻¹ *
          ((Matrix.GeneralLinearGroup.det (H PP.1))⁻¹ * dBlk (blk2 r) 1 (H PP.1))) * (h2 PP.1 PP.2).2.unit := by
      ext
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
      exact hdet PP.1 PP.2 (h2 PP.1 PP.2).1
    rw [hu]
    simp only [map_mul, map_inv]
  · exact absurd (hcond.mp h1) h2
  · exact absurd (hcond.mpr h2) h1
  · rw [mul_zero]

end GlobalTheory.ParabolicDatum
