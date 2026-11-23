import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

noncomputable section

private def leadCols {N : ℕ} (m l : Fin N) (j : Fin (l.val + 1)) : Fin N :=
  if hj : j.val < l.val then ⟨j.val, lt_trans hj l.isLt⟩ else m

private lemma leadCols_strictMono {N : ℕ} (m l : Fin N) (h : l < m) :
    StrictMono (leadCols m l) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  have hlm : l.val < m.val := h
  unfold leadCols
  by_cases hi : i.val < l.val <;> by_cases hj : j.val < l.val <;>
    simp only [hi, hj, dite_true, dite_false, Fin.lt_def] <;> omega

private lemma leadCols_mem {N : ℕ} (m l : Fin N) (j : Fin (l.val + 1)) :
    leadCols m l j ∈ insert m (Finset.Iio l) := by
  unfold leadCols
  split_ifs with hj
  · exact Finset.mem_insert_of_mem (Finset.mem_Iio.2 (Fin.lt_def.2 hj))
  · exact Finset.mem_insert_self _ _

private lemma card_leadCols {N : ℕ} (m l : Fin N) (h : l < m) :
    (insert m (Finset.Iio l)).card = l.val + 1 := by
  rw [Finset.card_insert_of_notMem (by simp [not_lt.2 h.le]), Fin.card_Iio]

theorem unipotent_pluckerCoord_eq {R : Type} [CommRing R] {N : ℕ} (a : LowerPairs N → R)
    (m l : Fin N) (h : l < m) :
    pluckerCoord (firstRows (unipotentMatrix a) (l.val + 1) l.isLt) (insert m (Finset.Iio l)) =
      a ⟨(m, l), h⟩ := by
  have hc := card_leadCols m l h
  have hemb : ((insert m (Finset.Iio l)).orderEmbOfFin hc : Fin (l.val + 1) → Fin N) =
      leadCols m l :=
    (Finset.orderEmbOfFin_unique hc (leadCols_mem m l) (leadCols_strictMono m l h)).symm
  have hlm : l.val < m.val := h
  unfold pluckerCoord
  rw [dif_pos hc]
  set M := (firstRows (unipotentMatrix a) (l.val + 1) l.isLt).submatrix id
    ((insert m (Finset.Iio l)).orderEmbOfFin hc) with hM
  have hentry : ∀ i j : Fin (l.val + 1),
      M i j = unipotentMatrix a (Fin.castLE l.isLt i) (leadCols m l j) := by
    intro i j
    simp only [hM, Matrix.submatrix_apply, id, firstRows, hemb]
  have htri : M.IsUpperTriangular := by
    intro i j hji
    have hji' : j.val < i.val := hji
    rw [hentry]
    have hj : j.val < l.val := by have := i.isLt; omega
    simp only [unipotentMatrix, leadCols, hj, dite_true, Matrix.of_apply]
    rw [dif_neg, if_neg]
    · intro he; have := congrArg Fin.val he; simp at this; omega
    · intro hlt; have := Fin.lt_def.1 hlt; simp at this; omega
  rw [Matrix.det_of_isUpperTriangular htri, Fin.prod_univ_castSucc]
  have hone : ∀ i : Fin l.val, M i.castSucc i.castSucc = 1 := by
    intro i
    rw [hentry]
    have hi : (i.castSucc : Fin (l.val + 1)).val < l.val := by simp
    simp only [unipotentMatrix, leadCols, hi, dite_true, Matrix.of_apply]
    rw [dif_neg, if_pos]
    · ext; simp
    · intro hlt; have := Fin.lt_def.1 hlt; simp at this
  have hlast : M (Fin.last l.val) (Fin.last l.val) = a ⟨(m, l), h⟩ := by
    rw [hentry]
    have hl : ¬ (Fin.last l.val).val < l.val := by simp
    have hcast : (Fin.castLE l.isLt (Fin.last l.val) : Fin N) = l := by ext; simp
    simp only [unipotentMatrix, leadCols, hl, dite_false, Matrix.of_apply, hcast]
    rw [dif_pos h]
  rw [Finset.prod_eq_one (fun i _ => hone i), hlast, one_mul]

theorem unipotent_pluckerCoord_adjoin (R : Type) [CommRing R] (N : ℕ) :
    Algebra.adjoin R (Set.range fun x : Fin (N + 1) × Finset (Fin N) =>
        pluckerCoord (firstRows (genericUnipotent R N) x.1.val (Nat.le_of_lt_succ x.1.isLt)) x.2) =
      ⊤ := by
  rw [eq_top_iff, ← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
  rintro _ ⟨p, rfl⟩
  apply Algebra.subset_adjoin
  refine ⟨(⟨p.1.2.val + 1, Nat.succ_lt_succ p.1.2.isLt⟩, insert p.1.1 (Finset.Iio p.1.2)), ?_⟩
  exact unipotent_pluckerCoord_eq (fun q => (X q : MvPolynomial (LowerPairs N) R)) p.1.1 p.1.2 p.2

theorem UnipotentCoordinates.full : UnipotentCoordinates.Statement :=
  ⟨fun _ _ _ a m l h => unipotent_pluckerCoord_eq a m l h,
    fun R _ N => unipotent_pluckerCoord_adjoin R N⟩

theorem UnipotentCoordinates.proof (_h0 : UnipotentLeadingMinor.Statement) :
    UnipotentCoordinates.Statement :=
  UnipotentCoordinates.full

end

end GroundTheory.Heights₂.Heights.FlagBundles
