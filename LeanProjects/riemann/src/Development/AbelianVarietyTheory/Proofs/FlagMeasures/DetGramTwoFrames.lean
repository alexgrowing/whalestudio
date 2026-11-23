import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem det_fromBlocks_swapCols {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n R) :
    (Matrix.fromBlocks A B C D).det = (-1) ^ Fintype.card n * (Matrix.fromBlocks B A D C).det := by
  have h : Matrix.fromBlocks A B C D =
      Matrix.fromBlocks B A D C * (Matrix.fromBlocks (1 : Matrix n n R) 1 0 1 *
        Matrix.fromBlocks (1 : Matrix n n R) 0 (-1) 1 * Matrix.fromBlocks (1 : Matrix n n R) 1 0 1 *
        Matrix.fromBlocks (-1 : Matrix n n R) 0 0 1) := by
    simp [Matrix.fromBlocks_multiply]
  rw [h]
  simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, Matrix.det_neg, mul_one, one_mul]
  ring

theorem fromBlocks_updateRow_eq {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (Z Z' : Matrix n n R) (l : n) (a b c d : n → R) :
    ((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) (Sum.elim a b)).updateRow (Sum.inr l)
        (Sum.elim c d) =
      Matrix.fromBlocks (Z.updateRow l a) ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) (Z'.updateRow l d) := by
  ext (i | i) (j | j) <;> by_cases h : i = l <;> simp [Matrix.updateRow_apply, h]

theorem det_updateRow_last_single {R : Type} [CommRing R] (r : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (t : R) :
    (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) t)).det =
      t * (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · have : (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) t)).submatrix
        (Fin.last r).succAbove (Fin.last r).succAbove =
        Z.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Matrix.updateRow_apply, Fin.succAbove_last, Fin.castSucc_ne_last]
    rw [this]
    simp [← two_mul, pow_mul]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem det_fromBlocks_rowBlocks {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (Z Z' : Matrix n n R) (l : n) (b c : n → R) :
    (Matrix.fromBlocks Z ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) Z').det =
      Z.det * Z'.det - (Z.updateRow l c).det * (Z'.updateRow l b).det := by
  set F : (n ⊕ n → R) → (n ⊕ n → R) → R := fun u v =>
    (((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) u).updateRow (Sum.inr l) v).det with hF
  have hz : (0 : Matrix n n R).updateRow l 0 = 0 := by
    ext i j; simp [Matrix.updateRow_apply]
  have hz0 : ∀ X : Matrix n n R, (X.updateRow l 0).det = 0 := fun X =>
    Matrix.det_eq_zero_of_row_eq_zero l (by simp)
  have add2 : ∀ u v w, F u (v + w) = F u v + F u w := fun u v w => Matrix.det_updateRow_add _ _ _ _
  have add1 : ∀ u v w, F (u + v) w = F u w + F v w := fun u v w => by
    simp only [hF]
    have hne : (Sum.inl l : n ⊕ n) ≠ Sum.inr l := by simp
    rw [Matrix.updateRow_comm _ hne, Matrix.updateRow_comm _ hne, Matrix.updateRow_comm _ hne]
    exact Matrix.det_updateRow_add _ _ _ _
  have swap : ∀ u v, F u v = - F v u := fun u v => by
    simp only [hF]
    have hne : (Sum.inl l : n ⊕ n) ≠ Sum.inr l := by simp
    have : ((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) u).updateRow (Sum.inr l) v =
        (((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) v).updateRow (Sum.inr l) u).submatrix
          (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
      ext i j
      by_cases h1 : i = Sum.inl l
      · subst h1; simp [Matrix.updateRow_apply]
      · by_cases h2 : i = Sum.inr l
        · subst h2; simp [Matrix.updateRow_apply]
        · simp [Matrix.updateRow_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, h1, h2]
    rw [this, Matrix.det_permute, Equiv.Perm.sign_swap hne]
    simp
  have val : ∀ a b c d : n → R, F (Sum.elim a b) (Sum.elim c d) =
      (Matrix.fromBlocks (Z.updateRow l a) ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) (Z'.updateRow l d)).det := fun a b c d => by
    simp only [hF, fromBlocks_updateRow_eq]
  have e : ∀ a b : n → R, Sum.elim a b = Sum.elim a (0 : n → R) + Sum.elim (0 : n → R) b := by
    intro a b; ext (i | i) <;> simp
  have h0 := val (Z l) b c (Z' l)
  rw [Matrix.updateRow_eq_self, Matrix.updateRow_eq_self] at h0
  rw [← h0, e (Z l) b, e c (Z' l), add1, add2, add2, swap (Sum.elim 0 b) (Sum.elim c 0)]
  simp only [val, hz, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, hz0,
    Matrix.updateRow_eq_self]
  ring

theorem det_gram_two_frames {R : Type} [CommRing R] (r : ℕ)
    (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (T T' : R) :
    (Matrix.fromBlocks (Matrix.single (Fin.last r) (Fin.last r) (-T)) Z Z'
      (Matrix.single (Fin.last r) (Fin.last r) (-T'))).det =
      (-1) ^ (r + 1) * (Z.det * Z'.det - T * T' *
        ((Z.submatrix Fin.castSucc Fin.castSucc).det *
          (Z'.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have hs : ∀ t : R, Matrix.single (Fin.last r) (Fin.last r) t =
      (0 : Matrix (Fin (r + 1)) (Fin (r + 1)) R).updateRow (Fin.last r)
        (Pi.single (Fin.last r) t) := by
    intro t
    ext i j
    simp only [Matrix.updateRow_apply, Matrix.single_apply, Pi.single_apply, Matrix.zero_apply]
    by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;>
      simp [hi, hj, eq_comm]
  rw [det_fromBlocks_swapCols, hs, hs, det_fromBlocks_rowBlocks, det_updateRow_last_single,
    det_updateRow_last_single, Fintype.card_fin]
  ring

end GlobalTheory.HL
