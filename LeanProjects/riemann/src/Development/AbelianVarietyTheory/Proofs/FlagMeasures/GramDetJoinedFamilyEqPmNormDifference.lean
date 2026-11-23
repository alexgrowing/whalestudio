import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.GramDet

theorem det_sub_single {E : Type} [CommRing E] {n : Type} [Fintype n] [DecidableEq n]
    (Y : Matrix n n E) (l : n) (d : E) :
    (Y - Matrix.single l l d).det = Y.det - d * Y.adjugate l l := by
  have h : Y - Matrix.single l l d = Y.updateRow l (Y l + (-d) • (Pi.single l 1 : n → E)) := by
    ext i j
    by_cases hi : i = l
    · subst hi
      by_cases hj : j = i
      · subst hj; simp [sub_eq_add_neg]
      · simp [hj, Ne.symm hj]
    · simp [Matrix.updateRow_ne hi, Ne.symm hi]
  rw [h, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    Matrix.adjugate_apply]
  ring

theorem det_blocks_single {E : Type} [CommRing E] {n : Type} [Fintype n] [DecidableEq n]
    (Z Y : Matrix n n E) (l : n) (c c' : E) (hZ : IsUnit Z.det) :
    (Matrix.fromBlocks Z (Matrix.single l l c) (Matrix.single l l c') Y).det
      = Z.det * Y.det - c * c' * (Z.adjugate l l * Y.adjugate l l) := by
  letI := Matrix.invertibleOfIsUnitDet Z hZ
  rw [Matrix.det_fromBlocks₁₁, Matrix.single_mul_mul_single, det_sub_single]
  have h : Z.det * (⅟Z) l l = Z.adjugate l l := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
      Ring.mul_inverse_cancel _ hZ, one_mul]
  rw [← h]; ring

theorem det_blocks_swap {E : Type} [CommRing E] {n : Type} [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n E) :
    (Matrix.fromBlocks A B C D).det = (Matrix.fromBlocks B A D C).det ∨
    (Matrix.fromBlocks A B C D).det = -(Matrix.fromBlocks B A D C).det := by
  have h := Matrix.det_permute' (Equiv.sumComm n n) (Matrix.fromBlocks B A D C)
  have h2 : (Matrix.fromBlocks B A D C).submatrix id (Equiv.sumComm n n)
      = Matrix.fromBlocks A B C D := by
    ext (i | i) (j | j) <;> rfl
  rw [h2] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm n n)) with h1 | h1
  · left; rw [h, h1]; simp
  · right; rw [h, h1]; simp

theorem adjugate_last {E : Type} [CommRing E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Z.adjugate (Fin.last r) (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, ← two_mul, pow_mul]
  simp

theorem det_gram_sum_elim {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F) (hf : ∀ a b, H.h (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E T) else 0) (hf' : ∀ a b, H.h (f' a) (f' b) = if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E T') else 0) (hD : IsUnit (H.Dl f f' (r + 1))) : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' ∨ (H.gram (Sum.elim f f')).det = -H.Gdet f f' T T' := by
  set Z := H.Zhat f f' with hZ
  have hD1 : H.Dl f f' (r + 1) = Z.det := by
    simp [HermSp.Dl, hZ]
  have hD0 : H.Dl f f' r = Z.adjugate (Fin.last r) (Fin.last r) := by
    rw [adjugate_last]
    simp only [HermSp.Dl, Nat.le_succ, dif_pos]
    rfl
  set c : E →+* E := (M.L.cj : E →+* E) with hc
  have hg : H.gram (Sum.elim f f') = Matrix.fromBlocks
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T))) Z (c.mapMatrix Z).transpose
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T'))) := by
    ext (i | i) (j | j)
    · simp [HermSp.gram, hf, Matrix.single_apply, and_comm, eq_comm]
    · rfl
    · exact H.h_herm _ _
    · simp [HermSp.gram, hf', Matrix.single_apply, and_comm, eq_comm]
  have hG : H.Gdet f f' T T' = (Matrix.fromBlocks Z
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T)))
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T')))
      (c.mapMatrix Z).transpose).det := by
    rw [det_blocks_single _ _ _ _ _ (hD1 ▸ hD), Matrix.det_transpose, ← RingHom.map_det,
      ← Matrix.adjugate_transpose, ← RingHom.map_adjugate, HermSp.Gdet, hD1, hD0]
    simp [HermSp.normE, hc]
  rw [hg, hG]
  exact det_blocks_swap _ _ _ _

end GlobalTheory.GramDet
