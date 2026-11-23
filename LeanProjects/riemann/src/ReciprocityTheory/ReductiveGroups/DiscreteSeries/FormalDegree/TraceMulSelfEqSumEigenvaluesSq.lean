import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma pmat_entry_cases {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a b : Fin n) :
    pmat z a b = 0 ∨ ε a ≠ ε b := by
  unfold pmat
  split_ifs with h h'
  · exact Or.inr h.2
  · exact Or.inr (Ne.symm h'.2)
  · exact Or.inl rfl

lemma jsgn_ne {x y : Bool} (h : x ≠ y) :
    ((if y then 1 else -1 : ℂ)) = -(if x then 1 else -1) := by
  cases x <;> cases y <;> simp at h ⊢

lemma jsgn_ne_zero (x : Bool) : ((if x then 1 else -1 : ℂ)) ≠ 0 := by
  cases x <;> simp

theorem pmat_inP {ε : Fin n → Bool} (z : PCoord ε → ℂ) : inP ε (pmat z) := by
  have h2 : pmat z * Jm ε = -(Jm ε * pmat z) := by
    ext a b
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
    rcases pmat_entry_cases z a b with h | h
    · rw [h]
      simp
    · rw [jsgn_ne h]
      ring
  refine ⟨?_, h2⟩
  unfold inG
  rw [(pmat_isHermitian z).eq, h2]
  simp

theorem pmat_coords {ε : Fin n → Bool} (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) :
    pmat (fun ab : PCoord ε => X ab.1.1 ab.1.2) = X := by
  obtain ⟨hG, hJ⟩ := hX
  unfold inG at hG
  have hent : ∀ a b, X a b * (if ε b then 1 else -1) = -((if ε a then 1 else -1) * X a b) := by
    intro a b
    have h := congrFun (congrFun hJ a) b
    simpa [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] using h
  have hzero : ∀ a b, ε a = ε b → X a b = 0 := by
    intro a b hab
    have h := hent a b
    rw [hab] at h
    cases hb : ε b <;> simp [hb] at h <;>
      first
        | exact h
        | linear_combination h / 2
        | linear_combination (-1 / 2 : ℂ) * h
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    cases ε a <;> simp
  have hH : Xᴴ = X := by
    have h1 : Xᴴ * Jm ε = X * Jm ε := by
      rw [hJ]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = X * Jm ε * Jm ε := by rw [h1]
      _ = X := by rw [mul_assoc, hJJ, mul_one]
  ext a b
  unfold pmat
  split_ifs with h h'
  · rfl
  · have h3 := congrFun (congrFun hH a) b
    rw [Matrix.conjTranspose_apply] at h3
    exact h3
  · apply (hzero a b ?_).symm
    rcases lt_trichotomy a b with hab | hab | hab
    · by_contra hne
      exact h' ⟨hab, Ne.symm hne⟩
    · rw [hab]
    · by_contra hne
      exact h ⟨hab, hne⟩

def pmatHalfSq {ε : Fin n → Bool} (z : PCoord ε → ℂ) (ab : Fin n × Fin n) : ℝ :=
  if h : ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2 then ‖z ⟨ab, h⟩‖ ^ 2 else 0

lemma norm_pmat_sq {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a b : Fin n) :
    ‖pmat z a b‖ ^ 2 = pmatHalfSq z (a, b) + pmatHalfSq z (b, a) := by
  unfold pmat pmatHalfSq
  dsimp only
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => lt_asymm h1.1 h.1
    simp only [dif_pos h1, dif_neg h2, add_zero]
  · by_cases h2 : a < b ∧ ε b ≠ ε a
    · simp only [dif_neg h1, dif_pos h2, norm_star, zero_add]
    · simp only [dif_neg h1, dif_neg h2, norm_zero, add_zero]
      norm_num

lemma sum_pmatHalfSq {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∑ ab : Fin n × Fin n, pmatHalfSq z ab = ∑ ab : PCoord ε, ‖z ab‖ ^ 2 := by
  classical
  have e1 : ∑ ab : Fin n × Fin n, pmatHalfSq z ab =
      ∑ ab ∈ univ.filter (fun ab : Fin n × Fin n => ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2), pmatHalfSq z ab := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ab _ => ?_
    split_ifs with h
    · rfl
    · unfold pmatHalfSq
      rw [dif_neg h]
  rw [e1, Finset.sum_subtype (p := fun ab : Fin n × Fin n => ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2) _
    (fun ab => by simp) (pmatHalfSq z)]
  refine Finset.sum_congr rfl fun ab _ => ?_
  unfold pmatHalfSq
  rw [dif_pos ab.2]

theorem hs_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : hs (pmat z) = 2 * ∑ ab, ‖z ab‖ ^ 2 := by
  unfold S7.hs
  have e : ∀ i j, ‖pmat z i j‖ ^ 2 = pmatHalfSq z (i, j) + pmatHalfSq z (j, i) := norm_pmat_sq z
  simp only [e, Finset.sum_add_distrib]
  have hprod : ∑ i, ∑ j, pmatHalfSq z (i, j) = ∑ ab : Fin n × Fin n, pmatHalfSq z ab :=
    (Fintype.sum_prod_type' (fun i j => pmatHalfSq z (i, j))).symm
  have hswap : ∑ i, ∑ j, pmatHalfSq z (j, i) = ∑ i, ∑ j, pmatHalfSq z (i, j) := Finset.sum_comm
  rw [hswap, hprod, sum_pmatHalfSq]
  ring

lemma pmat_diag_zero {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a : Fin n) : pmat z a a = 0 := by
  simp [pmat]

theorem sum_pev {ε : Fin n → Bool} (z : PCoord ε → ℂ) : ∑ a, pev z a = 0 := by
  have h := (pmat_isHermitian z).trace_eq_sum_eigenvalues
  have htr : (pmat z).trace = 0 := by simp [Matrix.trace, pmat_diag_zero]
  rw [htr] at h
  unfold pev
  have h2 : (((∑ i, (pmat_isHermitian z).eigenvalues i : ℝ)) : ℂ) = 0 := by
    rw [Complex.ofReal_sum]
    exact h.symm
  have h3 := Complex.ofReal_eq_zero.mp h2
  convert h3 using 2

lemma trace_mul_self_eq_sum_eigenvalues_sq {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hA' : A = U * D * star U := hA.spectral_theorem
  have hsq : A * A = U * (D * D) * star U := by
    rw [hA']
    calc U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U := by
          simp only [mul_assoc]
      _ = U * (D * D) * star U := by rw [hUU, mul_one]; simp only [mul_assoc]
  rw [hsq, Matrix.trace_mul_comm, ← mul_assoc, hUU, one_mul, hD, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  simp [sq]

lemma trace_mul_self_eq_hs {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ((hs A : ℝ) : ℂ) := by
  unfold S7.hs
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hji : A j i = star (A i j) := by
    have h := congrFun (congrFun hA.eq j) i
    rw [Matrix.conjTranspose_apply] at h
    exact h.symm
  rw [hji, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem sum_pev_sq {ε : Fin n → Bool} (z : PCoord ε → ℂ) : ∑ a, pev z a ^ 2 = hs (pmat z) := by
  have h1 := trace_mul_self_eq_sum_eigenvalues_sq (pmat_isHermitian z)
  rw [trace_mul_self_eq_hs (pmat_isHermitian z)] at h1
  unfold pev
  exact_mod_cast h1.symm

theorem card_PCoord (ε : Fin n → Bool) : Fintype.card (PCoord ε) = pOf ε * qOf ε := by
  classical
  rw [Fintype.card_subtype, pOf, qOf, ← Finset.card_product]
  refine Finset.card_nbij' (fun ab => if ε ab.1 then ab else (ab.2, ab.1))
    (fun xy => (max xy.1 xy.2, min xy.1 xy.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h
    obtain ⟨hba, hne⟩ := h
    cases ha : ε a <;> cases hb : ε b <;> simp_all
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_setOf_eq] at h
    obtain ⟨hx, hy⟩ := h
    have hxy : x ≠ y := by
      intro e
      rw [e, hy] at hx
      exact Bool.false_ne_true hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [max_eq_right h.le, min_eq_left h.le]
      exact ⟨h, by rw [hx, hy]; decide⟩
    · rw [max_eq_left h.le, min_eq_right h.le]
      exact ⟨h, by rw [hx, hy]; decide⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h
    obtain ⟨hba, hne⟩ := h
    cases ha : ε a
    · simp only [ha, Bool.false_eq_true, if_false]
      rw [max_eq_right hba.le, min_eq_left hba.le]
    · simp only [ha, if_true]
      rw [max_eq_left hba.le, min_eq_right hba.le]
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_setOf_eq] at h
    obtain ⟨hx, hy⟩ := h
    have hxy : x ≠ y := by
      intro e
      rw [e, hy] at hx
      exact Bool.false_ne_true hx
    dsimp only
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [max_eq_right h.le, min_eq_left h.le]
      simp [hy]
    · rw [max_eq_left h.le, min_eq_right h.le]
      simp [hx]

end ReciprocityTheory.ChartRestriction.DS
