import Mathlib

namespace GlobalTheory

open MvPolynomial Matrix

noncomputable def hermGenericMatrix {κ : Type} [Field κ] (n : ℕ) (e : κ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) κ) :=
  Matrix.of fun i j => X (i, j) + X (j, i) + C e * (X (i, j) - X (j, i))

theorem hermGenericMatrix_map_eval {κ : Type} [Field κ] (n : ℕ) (e : κ)
    (u : Fin n × Fin n → κ) :
    (hermGenericMatrix n e).map (MvPolynomial.eval u) =
      Matrix.of fun i j => u (i, j) + u (j, i) + e * (u (i, j) - u (j, i)) := by
  ext i j
  simp [hermGenericMatrix]

theorem hermGenericMatrix_onto {κ : Type} [Field κ] [CharZero κ] (n : ℕ) (e : κ) (he : e ≠ 0)
    (y : Matrix (Fin n) (Fin n) κ) :
    ∃ u : Fin n × Fin n → κ, (hermGenericMatrix n e).map (MvPolynomial.eval u) = y := by
  refine ⟨fun p => (y p.1 p.2 + y p.2 p.1) / 4 + (y p.1 p.2 - y p.2 p.1) / (4 * e), ?_⟩
  rw [hermGenericMatrix_map_eval]
  ext i j
  simp only [Matrix.of_apply]
  field_simp
  ring

theorem eval_det_affine_matrix {κ ι : Type} [Field κ] {n : ℕ} (c d : Matrix (Fin n) (Fin n) κ)
    (G : Matrix (Fin n) (Fin n) (MvPolynomial ι κ)) (u : ι → κ) :
    MvPolynomial.eval u (c.map C * G + d.map C).det =
      (c * G.map (MvPolynomial.eval u) + d).det := by
  rw [RingHom.map_det, map_add, map_mul]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

theorem exists_hermitian_det_ne_zero_two :
    ∀ (E κ : Type) [Field E] [CharZero E] [Field κ] (σ : E →+* E) (φ : E →+* κ) (δ : E), δ ≠ 0 → σ δ = -δ → ∀ (n : ℕ) (c d y c' d' y' : Matrix (Fin n) (Fin n) κ), (c * y + d).det ≠ 0 → (c' * y' + d').det ≠ 0 → ∃ x : Matrix (Fin n) (Fin n) E, x.map σ = x.transpose ∧ (c * x.map φ + d).det ≠ 0 ∧ (c' * x.transpose.map φ + d').det ≠ 0 := by
  intro E κ _ _ _ σ φ δ hδ hσ n c d y c' d' y' h h'
  haveI : CharZero κ := (RingHom.charZero_iff φ.injective).mp inferInstance
  have he : φ δ ≠ 0 := (map_ne_zero φ).mpr hδ
  set G := hermGenericMatrix n (φ δ) with hG
  have h1 : (c.map C * G + d.map C).det ≠ 0 := by
    obtain ⟨u, hu⟩ := hermGenericMatrix_onto n (φ δ) he y
    intro h0
    have := eval_det_affine_matrix c d G u
    rw [h0, map_zero, hG, hu] at this
    exact h this.symm
  have h2 : (c'.map C * Gᵀ + d'.map C).det ≠ 0 := by
    obtain ⟨u, hu⟩ := hermGenericMatrix_onto n (φ δ) he y'ᵀ
    intro h0
    have := eval_det_affine_matrix c' d' Gᵀ u
    rw [h0, map_zero, Matrix.transpose_map, hG, hu, Matrix.transpose_transpose] at this
    exact h' this.symm
  have h12 := mul_ne_zero h1 h2
  have key : ∃ m : Fin n × Fin n → ℕ, MvPolynomial.eval (fun p => (m p : κ))
      ((c.map C * G + d.map C).det * (c'.map C * Gᵀ + d'.map C).det) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply h12
    apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → κ))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro x hx
    have hx' : ∀ p, ∃ m : ℕ, (m : κ) = x p := fun p => hx p (Set.mem_univ p)
    choose m hm using hx'
    have : x = fun p => (m p : κ) := funext fun p => (hm p).symm
    rw [this, map_zero]
    exact hcon m
  obtain ⟨m, hm⟩ := key
  rw [map_mul, eval_det_affine_matrix, eval_det_affine_matrix, Matrix.transpose_map, hG,
    hermGenericMatrix_map_eval] at hm
  let x : Matrix (Fin n) (Fin n) E := Matrix.of fun i j =>
    (m (i, j) : E) + (m (j, i) : E) + δ * ((m (i, j) : E) - (m (j, i) : E))
  have hx : x.map φ = Matrix.of fun i j =>
      (m (i, j) : κ) + (m (j, i) : κ) + φ δ * ((m (i, j) : κ) - (m (j, i) : κ)) := by
    ext i j
    simp [x]
  refine ⟨x, ?_, ?_, ?_⟩
  · ext i j
    simp only [x, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, map_add, map_mul,
      map_sub, map_natCast, hσ]
    ring
  · rw [hx]; exact left_ne_zero_of_mul hm
  · rw [Matrix.transpose_map, hx]; exact right_ne_zero_of_mul hm

end GlobalTheory
