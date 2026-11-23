import Mathlib

namespace UpperTheory.Reformulated.B.StringRepresentationDecomposition

open Matrix

section

variable {K : Type*} [NormedField K]

private def Small {a b : Type*} (A : Matrix a b K) : Prop := ∀ i j, ‖A i j‖ ≤ 1

private def Good {a : Type*} [Fintype a] [DecidableEq a] (A : Matrix a a K) : Prop :=
  Small A ∧ ∃ B : Matrix a a K, Small B ∧ A * B = 1

private def Smith {a : Type*} [Fintype a] [DecidableEq a] (M : Matrix a a K) : Prop :=
  ∃ (U V : Matrix a a K) (d : a → K), Good U ∧ Good V ∧ M = U * diagonal d * V

private lemma small_zero {a b : Type*} : Small (0 : Matrix a b K) := by
  intro i j; simp

private lemma small_one {a : Type*} [DecidableEq a] : Small (1 : Matrix a a K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

private lemma small_neg {a b : Type*} {A : Matrix a b K} (h : Small A) : Small (-A) := by
  intro i j; simpa using h i j

private lemma small_blocks {a b : Type*} {A : Matrix a a K} {B : Matrix a b K}
    {C : Matrix b a K} {D : Matrix b b K} (hA : Small A) (hB : Small B) (hC : Small C)
    (hD : Small D) : Small (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  exacts [hA i j, hB i j, hC i j, hD i j]

private lemma small_mul [IsUltrametricDist K] {a : Type*} [Fintype a] {A B : Matrix a a K}
    (hA : Small A) (hB : Small B) : Small (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro k _
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

private lemma good_one {a : Type*} [Fintype a] [DecidableEq a] : Good (1 : Matrix a a K) :=
  ⟨small_one, 1, small_one, Matrix.mul_one _⟩

private lemma good_mul [IsUltrametricDist K] {a : Type*} [Fintype a] [DecidableEq a]
    {A B : Matrix a a K} (hA : Good A) (hB : Good B) : Good (A * B) := by
  obtain ⟨h1, A', h2, h3⟩ := hA
  obtain ⟨h4, B', h5, h6⟩ := hB
  refine ⟨small_mul h1 h4, B' * A', small_mul h5 h2, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h6, Matrix.one_mul, h3]

private lemma good_submatrix {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {A : Matrix a a K} (hA : Good A) (f g : b ≃ a) :
    Good (A.submatrix f g) := by
  obtain ⟨h1, A', h2, h3⟩ := hA
  refine ⟨fun i j => h1 _ _, A'.submatrix g f, fun i j => h2 _ _, ?_⟩
  rw [Matrix.submatrix_mul_equiv, h3, Matrix.submatrix_one_equiv]

private lemma smith_submatrix {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {M : Matrix a a K} (hM : Smith M) (f g : b ≃ a) :
    Smith (M.submatrix f g) := by
  obtain ⟨U, V, d, hU, hV, rfl⟩ := hM
  refine ⟨U.submatrix f f, V.submatrix f g, d ∘ f, good_submatrix hU f f,
    good_submatrix hV f g, ?_⟩
  rw [← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

private lemma smith_mul [IsUltrametricDist K] {a : Type*} [Fintype a] [DecidableEq a]
    {L M R : Matrix a a K} (hL : Good L) (hM : Smith M) (hR : Good R) :
    Smith (L * M * R) := by
  obtain ⟨U, V, d, hU, hV, rfl⟩ := hM
  exact ⟨L * U, V * R, d, good_mul hL hU, good_mul hV hR, by simp only [Matrix.mul_assoc]⟩

private lemma good_lower {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {C : Matrix b a K} (hC : Small C) :
    Good (fromBlocks (1 : Matrix a a K) 0 C (1 : Matrix b b K)) := by
  refine ⟨small_blocks small_one small_zero hC small_one, fromBlocks 1 0 (-C) 1,
    small_blocks small_one small_zero (small_neg hC) small_one, ?_⟩
  simp [Matrix.fromBlocks_multiply]

private lemma good_upper {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {C : Matrix a b K} (hC : Small C) :
    Good (fromBlocks (1 : Matrix a a K) C 0 (1 : Matrix b b K)) := by
  refine ⟨small_blocks small_one hC small_zero small_one, fromBlocks 1 (-C) 0 1,
    small_blocks small_one (small_neg hC) small_zero small_one, ?_⟩
  simp [Matrix.fromBlocks_multiply]

private lemma good_diag {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {U : Matrix b b K} (hU : Good U) :
    Good (fromBlocks (1 : Matrix a a K) 0 0 U) := by
  obtain ⟨h1, U', h2, h3⟩ := hU
  refine ⟨small_blocks small_one small_zero small_zero h1, fromBlocks 1 0 0 U',
    small_blocks small_one small_zero small_zero h2, ?_⟩
  simp [Matrix.fromBlocks_multiply, h3]

private lemma smith_diag {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (c : a → K) {D : Matrix b b K} (hD : Smith D) :
    Smith (fromBlocks (diagonal c) 0 0 D) := by
  obtain ⟨U, V, d, hU, hV, rfl⟩ := hD
  refine ⟨fromBlocks 1 0 0 U, fromBlocks 1 0 0 V, Sum.elim c d, good_diag hU, good_diag hV, ?_⟩
  rw [← Matrix.fromBlocks_diagonal]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]

private lemma smith_step [IsUltrametricDist K] {b : Type*} [Fintype b] [DecidableEq b]
    (ih : ∀ D : Matrix b b K, Smith D) (N : Matrix (Unit ⊕ b) (Unit ⊕ b) K)
    (hN : ∀ i j, ‖N i j‖ ≤ ‖N (Sum.inl ()) (Sum.inl ())‖) : Smith N := by
  set x := N (Sum.inl ()) (Sum.inl ()) with hx
  by_cases h0 : x = 0
  · refine ⟨1, 1, 0, good_one, good_one, ?_⟩
    ext i j
    have := hN i j
    rw [h0, norm_zero] at this
    simp [norm_le_zero_iff.mp this, Matrix.diagonal_apply]
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr h0
  let C : Matrix b Unit K := Matrix.of fun i _ => N (Sum.inr i) (Sum.inl ()) / x
  let B : Matrix Unit b K := Matrix.of fun _ j => N (Sum.inl ()) (Sum.inr j) / x
  let D : Matrix b b K := Matrix.of fun i j => N (Sum.inr i) (Sum.inr j) -
    N (Sum.inr i) (Sum.inl ()) * N (Sum.inl ()) (Sum.inr j) / x
  have hC : Small C := fun i j => by
    simp only [C, Matrix.of_apply, norm_div]
    exact (div_le_one hpos).mpr (hN _ _)
  have hB : Small B := fun i j => by
    simp only [B, Matrix.of_apply, norm_div]
    exact (div_le_one hpos).mpr (hN _ _)
  have key : N = fromBlocks 1 0 C 1 * fromBlocks (diagonal fun _ => x) 0 0 D
      * fromBlocks 1 B 0 1 := by
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    ext (i | i) (j | j)
    · simp [hx]
    · simp [B, Matrix.mul_apply]
      field_simp
    · simp [C, Matrix.mul_apply, h0]
    · simp [B, C, D, Matrix.mul_apply]
      field_simp
      ring
  rw [key]
  exact smith_mul (good_lower hC) (smith_diag _ (ih D)) (good_upper hB)

private lemma smith_fin [IsUltrametricDist K] (n : ℕ) :
    ∀ M : Matrix (Fin n) (Fin n) K, Smith M := by
  induction n with
  | zero => exact fun M => ⟨1, 1, 0, good_one, good_one, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro M
    obtain ⟨⟨p, q⟩, hpq⟩ := Finite.exists_max (fun x : Fin (n + 1) × Fin (n + 1) => ‖M x.1 x.2‖)
    let e : Fin (n + 1) ≃ Unit ⊕ Fin n := Fintype.equivOfCardEq (by simp [add_comm])
    let f : Fin (n + 1) ≃ Unit ⊕ Fin n := e.trans (Equiv.swap (e p) (Sum.inl ()))
    let g : Fin (n + 1) ≃ Unit ⊕ Fin n := e.trans (Equiv.swap (e q) (Sum.inl ()))
    have hf : f.symm (Sum.inl ()) = p := by simp [f]
    have hg : g.symm (Sum.inl ()) = q := by simp [g]
    have h := smith_step ih (M.submatrix f.symm g.symm) (fun i j => by
      simp only [Matrix.submatrix_apply, hf, hg]
      exact hpq (_, _))
    have h2 := smith_submatrix h f g
    simpa using h2

private lemma good_gl {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Good A) :
    ∃ U : GL (Fin n) K, (↑U : Matrix (Fin n) (Fin n) K) = A ∧
      Small (↑U⁻¹ : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨_, B, h2, h3⟩ := hA
  exact ⟨⟨A, B, h3, mul_eq_one_comm.mp h3⟩, rfl, h2⟩

end

end UpperTheory.Reformulated.B.StringRepresentationDecomposition

theorem UpperTheory.Reformulated.B.StringRepresentationDecomposition.smith_gen.{u_1} :
    ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {n : ℕ} (P : GL (Fin n) K),
      ∃ (U : GL (Fin n) K) (V : GL (Fin n) K) (d : Fin n → K),
        (∀ (i j : Fin n), ‖(↑U : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
          (∀ (i j : Fin n), ‖(↑U⁻¹ : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
            (∀ (i j : Fin n), ‖(↑V : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
              (∀ (i j : Fin n), ‖(↑V⁻¹ : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
                (∀ (i : Fin n), d i ≠ (0 : K)) ∧
                  (↑P : Matrix (Fin n) (Fin n) K) =
                    (↑U : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d * (↑V : Matrix (Fin n) (Fin n) K) := by
  intro K _ _ n P
  obtain ⟨A, B, d, hA, hB, h⟩ := smith_fin n (↑P : Matrix (Fin n) (Fin n) K)
  obtain ⟨U, rfl, hU⟩ := good_gl hA
  obtain ⟨V, rfl, hV⟩ := good_gl hB
  refine ⟨U, V, d, hA.1, hU, hB.1, hV, ?_, h⟩
  have hdet : (↑P : Matrix (Fin n) (Fin n) K).det ≠ 0 := P.det_ne_zero
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  intro i
  exact Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul hdet)) i
    (Finset.mem_univ i)
