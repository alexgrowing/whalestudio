import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option autoImplicit false

namespace GlobalTheory.LieFilt.IntForm

theorem det_blockUni {R : Type} [CommRing R] {κ : Type} [Fintype κ] [DecidableEq κ] (bl : κ → ℕ) (N : Matrix κ κ R)
    (h : ∀ z z', ¬ bl z < bl z' → N z z' = (1 : Matrix κ κ R) z z') : N.det = 1 := by
  have ht : N.BlockTriangular bl := by
    intro i j hij
    rw [h i j (by omega), Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij
  rw [ht.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : N.toSquareBlock bl a = 1 := by
    ext i j
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, h i j (by rw [i.2, j.2]; exact lt_irrefl _)]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

theorem norm_det_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_one₀ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => h _ _)
  exact IsUltrametricDist.norm_intCast_le_one K _

theorem norm_le_one_of_mulVec {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) (y : n → K) (hy : ∀ i, ‖A.mulVec y i‖ ≤ 1) (i : n) :
    ‖y i‖ ≤ 1 := by
  have h1 : A.cramer (A.mulVec y) = A.det • y := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have h2 := congrFun h1 i
  rw [Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul] at h2
  have h3 : ‖(A.updateCol i (A.mulVec y)).det‖ ≤ 1 := by
    refine norm_det_le_one _ fun a b => ?_
    rw [Matrix.updateCol_apply]
    split_ifs
    · exact hy a
    · exact h a b
  rwa [h2, norm_mul, hd, one_mul] at h3

variable {κ : Type} [Fintype κ] (bl : κ → ℕ)

theorem blockUni_mul {R : Type} [CommRing R] {M N : Matrix κ κ R} (hM : BlockUni bl M) (hN : BlockUni bl N) :
    BlockUni bl (M * N) := by
  intro z z' h
  have : ∀ y, M z y * N y z' = (1 : Matrix κ κ R) z y * (1 : Matrix κ κ R) y z' := by
    intro y
    by_cases h1 : bl y < bl z'
    · have hne : z ≠ y := by rintro rfl; exact h h1
      rw [hM z y (by omega), Matrix.one_apply_ne hne, zero_mul, zero_mul]
    · rw [hN y z' h1]
      by_cases h2 : y = z'
      · subst h2; rw [hM z y h]
      · rw [Matrix.one_apply_ne h2, mul_zero, mul_zero]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun y _ => this y, ← Matrix.mul_apply, Matrix.mul_one]

theorem blockUni_inv {R : Type} [CommRing R] {M N : Matrix κ κ R} (hN : BlockUni bl N) (h : M * N = 1) :
    BlockUni bl M := by
  have ht : N.BlockTriangular bl := by
    intro i j hij
    rw [hN i j (by omega), Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij
  letI := invertibleOfLeftInverse N M h
  have hM : M.BlockTriangular bl := by
    rw [← Matrix.inv_eq_left_inv h]
    exact Matrix.blockTriangular_inv_of_blockTriangular ht
  intro z z' hz
  have : ∀ y, M z y * N y z' = M z y * (1 : Matrix κ κ R) y z' := by
    intro y
    by_cases h1 : bl y < bl z'
    · rw [hM (show bl y < bl z by omega), zero_mul, zero_mul]
    · rw [hN y z' h1]
  rw [← h, Matrix.mul_apply, Finset.sum_congr rfl fun y _ => this y, ← Matrix.mul_apply, Matrix.mul_one]

theorem mul_apply_blockUni {R : Type} [CommRing R] {α : Type} (P : Matrix α κ R) {N : Matrix κ κ R}
    (hN : BlockUni bl N) (k : ℕ) (a : α) (z' : κ) (hz : bl z' ≤ k) :
    (P * N) a z' = (∑ y : {y // bl y < k}, P a y * N y z') + if bl z' < k then 0 else P a z' := by
  rw [Matrix.mul_apply, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => bl y < k)]
  congr 1
  · exact Finset.sum_subtype _ (by simp) _
  · rw [Finset.sum_congr rfl (g := fun y => P a y * (1 : Matrix κ κ R) y z')
      fun y hy => by rw [hN y z' (by simp at hy; omega)]]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases h : bl z' < k <;> simp [h]

theorem minor_mul {R : Type} [CommRing R] {g : ℕ} (w : κ ≃ Fin g) (k : ℕ) (P : Matrix (Fin g) κ R) {N : Matrix κ κ R}
    (hN : BlockUni bl N) : minor bl w k (P * N) = minor bl w k P := by
  unfold minor
  have : (((P * N).submatrix w id).toSquareBlockProp fun z => bl z < k) =
      ((P.submatrix w id).toSquareBlockProp fun z => bl z < k) * (N.toSquareBlockProp fun z => bl z < k) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.toSquareBlockProp_def, Matrix.of_apply, Matrix.submatrix_apply, id]
    rw [mul_apply_blockUni bl P hN k _ _ j.2.le, if_pos j.2, add_zero]
  rw [this, Matrix.det_mul, det_blockUni (fun z : {z // bl z < k} => bl z) (N.toSquareBlockProp fun z => bl z < k),
    mul_one]
  intro z z' h
  rw [Matrix.toSquareBlockProp_def, Matrix.of_apply, hN z z' h]
  simp [Matrix.one_apply, Subtype.ext_iff]

theorem norm_mul_le_one : ∀ {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ}
    (P : Matrix (Fin g) κ K) (w : κ ≃ Fin g), IntAdapted bl P → (∀ k : ℕ, ‖minor bl w k P‖ = 1) →
    ∀ Q : Matrix κ κ K, BlockUni bl Q → (∀ z z', bl z < bl z' → (P * Q) (w z) z' = 0) → ∀ b z, ‖(P * Q) b z‖ ≤ 1 := by
  intro K _ _ κ _ bl g P w ⟨N, C', hN, hC, _, _, h2⟩ hm Q hQ h0
  have h3 : (C' * P) * N = 1 := by rw [Matrix.mul_assoc]; exact h2
  have h4 : N * (C' * P) = 1 := mul_eq_one_comm.mp h3
  have hM : BlockUni bl (C' * P * Q) := blockUni_mul bl (blockUni_inv bl hN h3) hQ
  have hPQ : P * Q = (P * N) * (C' * P * Q) := by
    rw [Matrix.mul_assoc P N, ← Matrix.mul_assoc N, h4, Matrix.one_mul]
  rw [hPQ] at h0 ⊢
  have hm' : ∀ k, ‖minor bl w k (P * N)‖ = 1 := fun k => by rw [minor_mul bl w k P hN]; exact hm k
  generalize P * N = C at *
  generalize C' * P * Q = M at *
  have hI : ∀ z z', ‖M z z'‖ ≤ 1 := by
    intro z z'
    by_cases h : bl z < bl z'
    · refine norm_le_one_of_mulVec ((C.submatrix w id).toSquareBlockProp fun y => bl y < bl z')
        (fun i j => hC _ _) (hm' _) (fun y => M y z') (fun i => ?_) ⟨z, h⟩
      have h5 := h0 i z' i.2
      rw [mul_apply_blockUni bl C hM (bl z') _ _ le_rfl, if_neg (lt_irrefl _)] at h5
      have h6 := eq_neg_of_add_eq_zero_left h5
      change ‖∑ y : {y // bl y < bl z'}, C (w i) y * M y z'‖ ≤ 1
      rw [h6, norm_neg]
      exact hC _ _
    · rw [hM z z' h, Matrix.one_apply]
      split_ifs <;> simp
  intro b z
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hC _ _) (norm_nonneg _) (hI _ _)

end GlobalTheory.LieFilt.IntForm
