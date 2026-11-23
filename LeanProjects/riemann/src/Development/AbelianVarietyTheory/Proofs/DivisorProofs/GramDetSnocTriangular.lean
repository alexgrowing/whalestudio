import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open scoped Matrix

namespace GlobalTheory

section GramTri

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem gramTri_form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm σ y (a • x), h.smul_right, map_mul, h.conj_symm]

theorem gramTri_form_sum_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type} (s : Finset ι)
    (f : ι → V) : h.form σ x (∑ k ∈ s, f k) = ∑ k ∈ s, h.form σ x (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := h.smul_right σ 0 x 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, h.add_right, ih, Finset.sum_insert ha]

theorem gramTri_form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (z : V) {ι : Type} (s : Finset ι)
    (f : ι → V) : h.form σ (∑ k ∈ s, f k) z = ∑ k ∈ s, h.form σ (f k) z := by
  rw [← h.conj_symm σ z, gramTri_form_sum_right, map_sum]
  simp only [h.conj_symm]

theorem hermFam_gram_matrix_change (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (e : Fin n → V)
    (P : Matrix (Fin n) (Fin n) K) :
    h.gram σ (fun j => ∑ k, P k j • e k) = (P.map σ)ᴴ * h.gram σ e * P.map σ := by
  ext i j
  simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, gramTri_form_sum_left, gramTri_form_sum_right, gramTri_form_smul_left,
    h.smul_right, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Complex.star_def]
  ring

def triChangeMatrix {i : ℕ} (d : Fin i → K) (c : Fin (i + 1) → K) :
    Matrix (Fin (i + 1)) (Fin (i + 1)) K :=
  Matrix.of fun k j => Fin.snoc (α := fun _ => K) (fun j' => if k = j'.castSucc then d j' else 0) (c k) j

theorem triChangeMatrix_family {i : ℕ} (e : Fin (i + 1) → V) (d : Fin i → K) (c : Fin (i + 1) → K) :
    (Fin.snoc (α := fun _ => V) (fun j => d j • e j.castSucc) (∑ k, c k • e k)) =
      fun j => ∑ k, triChangeMatrix d c k j • e k := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [triChangeMatrix]
  | cast j =>
    simp only [triChangeMatrix, Matrix.of_apply, Fin.snoc_castSucc, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq']
    simp

theorem triChangeMatrix_det {i : ℕ} (d : Fin i → K) (c : Fin (i + 1) → K) :
    (triChangeMatrix d c).det = (∏ j, d j) * c (Fin.last i) := by
  have hT : (triChangeMatrix d c).BlockTriangular id := by
    intro k j hjk
    simp only [id] at hjk
    induction j using Fin.lastCases with
    | last => exact absurd hjk (not_lt.2 (Fin.le_last k))
    | cast j =>
      simp only [triChangeMatrix, Matrix.of_apply, Fin.snoc_castSucc]
      rw [if_neg (ne_of_gt hjk)]
  rw [Matrix.det_of_upperTriangular hT, Fin.prod_univ_castSucc]
  simp [triChangeMatrix]

theorem hermFam_gram_det_triangular (h : HermFam K V) (σ : K →+* ℂ) {i : ℕ} (e : Fin (i + 1) → V)
    (d : Fin i → K) (c : Fin (i + 1) → K) :
    (h.gram σ (Fin.snoc (fun j => d j • e j.castSucc) (∑ k, c k • e k))).det.re =
      (∏ j, ‖σ (d j)‖ ^ 2) * ‖σ (c (Fin.last i))‖ ^ 2 * (h.gram σ e).det.re := by
  rw [triChangeMatrix_family, hermFam_gram_matrix_change, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose]
  have hmap : ((triChangeMatrix d c).map σ).det = σ (triChangeMatrix d c).det := by
    rw [RingHom.map_det]; rfl
  rw [hmap, triChangeMatrix_det]
  set z := σ ((∏ j, d j) * c (Fin.last i))
  have hz : star z * (h.gram σ e).det * z = ((‖z‖ ^ 2 : ℝ) : ℂ) * (h.gram σ e).det := by
    rw [mul_comm (star z * _) z, ← mul_assoc, Complex.star_def, Complex.mul_conj']
    push_cast; ring
  rw [hz, Complex.re_ofReal_mul]
  simp only [z, map_mul, map_prod, norm_mul, norm_prod, mul_pow, Finset.prod_pow]

end GramTri

end GlobalTheory
