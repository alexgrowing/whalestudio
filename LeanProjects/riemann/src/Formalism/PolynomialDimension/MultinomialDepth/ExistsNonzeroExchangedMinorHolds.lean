import Formalism.PolynomialDimension.FrameSum

open scoped BigOperators
open Finset Matrix

namespace Formalism.CountingSumsFrames

theorem submatrix_swapCol {R : Type} [CommRing R] {r k : ℕ} (h : r ≤ k) (H : Matrix (Fin r) (Fin k) R)
    (i : Fin r) (c : Fin k) :
    H.submatrix id (swapCol r k h i c) = (H.submatrix id (Fin.castLE h)).updateCol i (fun m => H m c) := by
  ext m j
  by_cases hj : j = i
  · subst hj
    simp [swapCol]
  · simp [swapCol, hj]

theorem piMinor_map {p r k : ℕ} [Fact p.Prime] {F A : Type} [Field F] [CharP F p] [CommRing A] [Algebra F A]
    [Nontrivial A] (H : Matrix (Fin r) (Fin k) F) (pos : Fin r → ℕ) (t : Fin r → Fin r → A) (zj : ℕ)
    (cols : Fin r → Fin k) (hpos : ∀ l, pos l ≤ zj) :
    piMinor p r k (H.map (algebraMap F A)) pos t zj cols =
      (Matrix.of fun l m => t l m ^ p ^ (zj - pos l)).det *
        algebraMap F A ((H.submatrix id cols).det ^ p ^ zj) := by
  have : CharP A p := charP_of_injective_algebraMap (algebraMap F A).injective p
  have : ExpChar A p := ExpChar.prime (Fact.out : p.Prime)
  have : ExpChar F p := ExpChar.prime (Fact.out : p.Prime)
  let g : F →+* A := (algebraMap F A).comp (iterateFrobenius F p zj)
  have hg : ∀ x, g x = algebraMap F A (x ^ p ^ zj) := fun x => by
    simp [g, iterateFrobenius_def]
  have hmat : (Matrix.of fun l c' => (frameRow p r k (H.map (algebraMap F A)) (pos l) (t l) (cols c')) ^ p ^ (zj - pos l)) =
      (Matrix.of fun l m => t l m ^ p ^ (zj - pos l)) * (g.mapMatrix (H.submatrix id cols)) := by
    ext l c'
    simp only [Matrix.of_apply, frameRow, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply,
      RingHom.mapMatrix_apply, Matrix.submatrix_apply, id, hg]
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le (hpos l), map_pow]
  unfold piMinor
  rw [hmat, Matrix.det_mul, ← RingHom.map_det, hg]

end Formalism.CountingSumsFrames
