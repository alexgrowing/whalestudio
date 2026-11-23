import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) : Fin (a + 1) → Fin n :=
  fun c => if h : (c : ℕ) < a then ⟨c, by have := a.2; omega⟩ else b

def pivotMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) : R :=
  (M.submatrix (Fin.castLE (by have := a.2; omega)) (pivotCols a b)).det

def leadMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) : R :=
  pivotMinor M a (Fin.castLE (Nat.sub_le n 1) a)

def pivotMatrix {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r b => if h : (r : ℕ) < n - 1 then pivotMinor M ⟨r, h⟩ b else 0

theorem pivotCols_strictMono {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    StrictMono (pivotCols a b) := by
  intro c d hcd
  have hcd' : (c : ℕ) < d := hcd
  simp only [pivotCols]
  split_ifs with h1 h2 h2
  · exact Fin.mk_lt_mk.mpr hcd'
  · exact Fin.mk_lt_mk.mpr (by omega)
  · omega
  · omega

theorem card_image_pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    (Finset.univ.image (pivotCols a b)).card = a + 1 := by
  rw [Finset.card_image_of_injective _ (pivotCols_strictMono a b hab).injective, Finset.card_univ, Fintype.card_fin]

theorem pivotMinor_eq_flagMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hab : (a : ℕ) ≤ b) :
    pivotMinor M a b = flagMinor M a ⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩ := by
  unfold pivotMinor flagMinor
  congr 2
  exact (Finset.orderEmbOfFin_unique (card_image_pivotCols a b hab) (fun c => Finset.mem_image_of_mem _ (Finset.mem_univ c))
    (pivotCols_strictMono a b hab))

theorem pivotMinor_eq_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hba : (b : ℕ) < a) : pivotMinor M a b = 0 := by
  unfold pivotMinor
  refine Matrix.det_zero_of_column_eq (i := ⟨b, by omega⟩) (j := Fin.last a) (fun h => by
    have := congrArg Fin.val h; simp at this; omega) fun k => ?_
  simp [pivotCols, hba]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
