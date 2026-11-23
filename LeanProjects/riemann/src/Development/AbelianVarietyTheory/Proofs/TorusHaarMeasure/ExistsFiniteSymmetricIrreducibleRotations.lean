import Mathlib

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory
namespace HypRot

variable {r : ℕ}

noncomputable def offN (j k : Fin r) (u : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.single j k u + Matrix.single k j (star u)

noncomputable def projP (j k : Fin r) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.single j j 1 + Matrix.single k k 1

noncomputable def rot (j k : Fin r) (u : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + (1 / 4 : ℂ) • projP j k + (3 / 4 : ℂ) • offN j k u

lemma offN_neg (j k : Fin r) (u : ℂ) : offN j k (-u) = - offN j k u := by
  simp only [offN, star_neg, Matrix.single_neg, neg_add]

lemma offN_sq {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    offN j k u * offN j k u = projP j k := by
  have hu' : star u * u = 1 := by rw [mul_comm]; exact hu
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, hu, hu',
    zero_add, add_zero]
  exact add_comm _ _

lemma projP_offN {j k : Fin r} (h : j ≠ k) (u : ℂ) :
    projP j k * offN j k u = offN j k u := by
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, one_mul,
    zero_add, add_zero]

lemma offN_projP {j k : Fin r} (h : j ≠ k) (u : ℂ) :
    offN j k u * projP j k = offN j k u := by
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true,
    mul_one, zero_add, add_zero]
  exact add_comm _ _

lemma projP_sq {j k : Fin r} (h : j ≠ k) : projP j k * projP j k = projP j k := by
  simp only [projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, one_mul,
    zero_add, add_zero]

lemma rot_mul_neg {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    rot j k u * rot j k (-u) = 1 := by
  have hPP := projP_sq h
  have hPN := projP_offN h u
  have hNP := offN_projP h u
  have hNN := offN_sq h hu
  simp only [rot, offN_neg, smul_neg, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, mul_neg, hPP, hPN, hNP, hNN]
  module

lemma rot_sq_sub {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    offN j k u = (4 / 15 : ℂ) • (rot j k u * rot j k u - rot j k (-u) * rot j k (-u)) := by
  have hPP := projP_sq h
  have hPN := projP_offN h u
  have hNP := offN_projP h u
  have hNN := offN_sq h hu
  simp only [rot, offN_neg, smul_neg, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, mul_neg, neg_mul, hPP, hPN, hNP, hNN]
  module

lemma rot_inv {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    (rot j k u)⁻¹ = rot j k (-u) := Matrix.inv_eq_right_inv (rot_mul_neg h hu)

lemma rot_det {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    (rot j k u).det ≠ 0 := (Matrix.isUnit_det_of_right_inverse (rot_mul_neg h hu)).ne_zero

lemma rot_herm (j k : Fin r) (u : ℂ) : (rot j k u).IsHermitian := by
  unfold Matrix.IsHermitian
  simp only [rot, offN, projP, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_single, star_star, star_one, smul_add]
  have h4 : star (1 / 4 : ℂ) = 1 / 4 := by simp
  have h34 : star (3 / 4 : ℂ) = 3 / 4 := by simp
  rw [h4, h34]
  abel

private lemma diagonal_mul_single (d : Fin r → ℂ) (i j : Fin r) (c : ℂ) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

private lemma single_mul_diagonal (d : Fin r → ℂ) (i j : Fin r) (c : ℂ) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

lemma diag_rot {j k : Fin r} (d : Fin r → ℂ) (hd : d j = - d k) (u : ℂ) :
    Matrix.diagonal d * rot j k u = rot j k (-u) * Matrix.diagonal d := by
  simp only [rot, offN, projP, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, diagonal_mul_single, single_mul_diagonal, star_neg, hd]
  simp only [mul_one, one_mul, neg_mul, mul_neg, neg_neg, mul_comm u (d k), mul_comm (star u) (d k)]

lemma rot_unitary {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1)
    (d : Fin r → ℂ) (hd : d j = - d k) :
    (rot j k u)ᵀ * Matrix.diagonal d * (rot j k u).map (starRingEnd ℂ) = Matrix.diagonal d := by
  have hT : (rot j k u)ᵀ = rot j k (star u) := by
    simp only [rot, offN, projP, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_single, star_star, smul_add]
    abel
  have hC : (rot j k u).map (starRingEnd ℂ) = (rot j k u)ᵀ := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    exact (rot_herm j k u).apply b a
  have hu' : star u * star (star u) = 1 := by rw [star_star, mul_comm]; exact hu
  rw [hC, hT, Matrix.mul_assoc, diag_rot d hd, ← Matrix.mul_assoc, rot_mul_neg h hu',
    Matrix.one_mul]

end HypRot

open HypRot in

theorem exists_finite_symmetric_irreducible_rotations :
    (∀ (r p : ℕ), 0 < p → p < r → ∀ W : Submodule ℂ (Fin r → ℂ), (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W, (Matrix.single j k (1 : ℂ)).mulVec v ∈ W ∧ (Matrix.single k j (1 : ℂ)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by
  intro H r p hp hpr
  classical
  have hne : ∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → j ≠ k := by
    intro j k hj hk e
    have := congrArg Fin.val e
    omega
  have hUs : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ),
      u * star u = 1 ∧ -u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;>
      simp [Complex.ext_iff]
  refine ⟨((Finset.univ.filter fun jk : Fin r × Fin r => (jk.1 : ℕ) < p ∧ p ≤ (jk.2 : ℕ)) ×ˢ
      ({1, -1, Complex.I, -Complex.I} : Finset ℂ)).image (fun x => rot x.1.1 x.1.2 x.2),
      ?_, ?_, ?_, ?_⟩
  · refine ⟨rot ⟨0, by omega⟩ ⟨p, hpr⟩ 1, Finset.mem_image.mpr ⟨((⟨0, by omega⟩, ⟨p, hpr⟩), 1), ?_, rfl⟩⟩
    simp [hp]
  · intro a ha
    obtain ⟨⟨⟨j, k⟩, u⟩, hx, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨hj, hk⟩, hu⟩ := hx
    refine ⟨rot_herm j k u, rot_det (hne j k hj hk) (hUs u hu).1, ?_⟩
    rw [rot_inv (hne j k hj hk) (hUs u hu).1]
    exact Finset.mem_image.mpr ⟨((j, k), -u), by simp [hj, hk, (hUs u hu).2], rfl⟩
  · intro W hW
    apply H r p hp hpr W
    intro j k hj hk v hv
    have hjk := hne j k hj hk
    have hmem : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ), rot j k u ∈
        ((Finset.univ.filter fun jk : Fin r × Fin r => (jk.1 : ℕ) < p ∧ p ≤ (jk.2 : ℕ)) ×ˢ
        ({1, -1, Complex.I, -Complex.I} : Finset ℂ)).image (fun x => rot x.1.1 x.1.2 x.2) := by
      intro u hu
      exact Finset.mem_image.mpr ⟨((j, k), u), by simp [hj, hk, hu], rfl⟩
    have hN : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ), (offN j k u).mulVec v ∈ W := by
      intro u hu
      rw [rot_sq_sub hjk (hUs u hu).1, Matrix.smul_mulVec, Matrix.sub_mulVec]
      exact W.smul_mem _ (W.sub_mem (hW _ (hmem u hu) v hv) (hW _ (hmem _ (hUs u hu).2) v hv))
    have h1 : (1 : ℂ) ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by simp
    have hI : Complex.I ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by simp
    have hII : Complex.I * star Complex.I = 1 := by
      rw [Complex.star_def, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg]
    have hsI : Complex.I • offN j k Complex.I = -Matrix.single j k (1 : ℂ) + Matrix.single k j 1 := by
      rw [offN, smul_add, Matrix.smul_single, Matrix.smul_single, smul_eq_mul, smul_eq_mul,
        Complex.I_mul_I, hII, Matrix.single_neg]
    have h1' : offN j k (1 : ℂ) = Matrix.single j k 1 + Matrix.single k j 1 := by
      rw [offN, star_one]
    have e1 : Matrix.single j k (1 : ℂ) = (1 / 2 : ℂ) • (offN j k 1 - Complex.I • offN j k Complex.I) := by
      rw [hsI, h1']
      module
    have e2 : Matrix.single k j (1 : ℂ) = (1 / 2 : ℂ) • (offN j k 1 + Complex.I • offN j k Complex.I) := by
      rw [hsI, h1']
      module
    constructor
    · rw [e1, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
      exact W.smul_mem _ (W.sub_mem (hN 1 h1) (W.smul_mem _ (hN _ hI)))
    · rw [e2, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec]
      exact W.smul_mem _ (W.add_mem (hN 1 h1) (W.smul_mem _ (hN _ hI)))
  · intro a ha
    obtain ⟨⟨⟨j, k⟩, u⟩, hx, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨hj, hk⟩, hu⟩ := hx
    have hjk := hne j k hj hk
    have hd : (fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1) j =
        -(fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1) k := by
      simp [hj, not_lt.mpr hk]
    refine ⟨rot_unitary hjk (hUs u hu).1 _ hd, Matrix.diagonal fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1, ?_, ?_⟩
    · rw [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> simp
    · rw [rot_inv hjk (hUs u hu).1]
      exact diag_rot _ hd u

end GlobalTheory
