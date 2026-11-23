import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace GlobalTheory

theorem abs_log_norm_sub_re_sub_one_le {μ : ℂ} {t : ℝ} (hμ : ‖μ - 1‖ ≤ t) (ht : t < 1) :
    μ ≠ 0 ∧ |Real.log ‖μ‖ - (μ - 1).re| ≤ t ^ 2 / (2 * (1 - t)) := by
  have h1 : ‖μ - 1‖ < 1 := hμ.trans_lt ht
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp at h1
  · have h := Complex.norm_log_one_add_sub_self_le h1
    rw [add_sub_cancel] at h
    have h2 : Real.log ‖μ‖ - (μ - 1).re = (Complex.log μ - (μ - 1)).re := by
      rw [Complex.sub_re (Complex.log μ), Complex.log_re]
    rw [h2]
    refine (Complex.abs_re_le_norm _).trans (h.trans ?_)
    have h0 := norm_nonneg (μ - 1)
    have h3 : (1 - ‖μ - 1‖)⁻¹ ≤ (1 - t)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    have h4 : ‖μ - 1‖ ^ 2 ≤ t ^ 2 := by gcongr
    have h5 : 0 ≤ (1 - ‖μ - 1‖)⁻¹ := inv_nonneg.2 (by linarith)
    calc ‖μ - 1‖ ^ 2 * (1 - ‖μ - 1‖)⁻¹ / 2 ≤ t ^ 2 * (1 - t)⁻¹ / 2 := by gcongr
      _ = t ^ 2 / (2 * (1 - t)) := by
        have : (1 - t) ≠ 0 := by linarith
        field_simp

theorem abs_log_norm_multisetProd_sub_le (s : Multiset ℂ) {t : ℝ} (ht : t < 1)
    (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ t) :
    s.prod ≠ 0 ∧ |Real.log ‖s.prod‖ - (s.sum - s.card).re| ≤
      s.card * (t ^ 2 / (2 * (1 - t))) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    obtain ⟨h0, h1⟩ := ih fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ)
    obtain ⟨h2, h3⟩ := abs_log_norm_sub_re_sub_one_le (hs a (Multiset.mem_cons_self a s)) ht
    refine ⟨by simp [h0, h2], ?_⟩
    rw [Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 h2) (norm_ne_zero_iff.2 h0)]
    have : Real.log ‖a‖ + Real.log ‖s.prod‖ - (a + s.sum - ((s.card + 1 : ℕ) : ℂ)).re =
        (Real.log ‖a‖ - (a - 1).re) + (Real.log ‖s.prod‖ - (s.sum - s.card).re) := by
      simp only [Complex.sub_re, Complex.add_re, Nat.cast_add, Nat.cast_one, Complex.one_re]
      ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith

section OpNorm

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem l2_opNorm_diagonal_sign_le {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1) :
    ‖(diagonal j : Matrix n n ℂ)‖ ≤ 1 := by
  rw [l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
  rcases hj k with h | h <;> simp [h]

theorem l2_opNorm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← diagonal_one]
  exact l2_opNorm_diagonal_sign_le fun _ => Or.inl rfl

omit [DecidableEq m] in

theorem l2_opNorm_map_star (A : Matrix m n ℂ) : ‖A.map star‖ = ‖A‖ := by
  have key : ∀ B : Matrix m n ℂ, ‖B.map star‖ ≤ ‖B‖ := by
    intro B
    rw [l2_opNorm_def (B.map star)]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h := l2_opNorm_mulVec B (WithLp.toLp 2 (star x.ofLp))
    have h1 : ‖(WithLp.toLp 2 (star x.ofLp) : EuclideanSpace ℂ n)‖ = ‖x‖ := by
      simp [EuclideanSpace.norm_eq]
    rw [h1] at h
    refine le_trans (le_of_eq ?_) h
    simp only [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← norm_star]
    congr 1
    simp [toEuclideanLin, mulVec, dotProduct]
  refine le_antisymm (key A) ?_
  have := key (A.map star)
  rwa [show (A.map star).map star = A by ext; simp] at this

theorem l2_opNorm_transpose (A : Matrix m n ℂ) : ‖Aᵀ‖ = ‖A‖ := by
  rw [← l2_opNorm_conjTranspose A, ← l2_opNorm_map_star Aᵀ]
  rfl

theorem l2_opNorm_submatrix_le (A : Matrix n n ℂ) {e : m → n} (he : Function.Injective e) :
    ‖A.submatrix e e‖ ≤ ‖A‖ := by
  set P : Matrix n m ℂ := (1 : Matrix n n ℂ).submatrix id e with hP
  have hPP : Pᴴ * P = 1 := by
    ext a b
    simp [hP, mul_apply, one_apply, he.eq_iff]
  have hA : A.submatrix e e = Pᴴ * A * P := by
    ext a b
    simp [hP, mul_apply, one_apply]
  have hn : ‖P‖ ≤ 1 := by
    have := l2_opNorm_conjTranspose_mul_self P
    rw [hPP] at this
    have h1 := l2_opNorm_one_le (n := m)
    nlinarith [norm_nonneg P]
  rw [hA]
  have h1 := l2_opNorm_mul (Pᴴ * A) P
  have h2 := l2_opNorm_mul Pᴴ A
  rw [l2_opNorm_conjTranspose] at h2
  have h3 := norm_nonneg A
  have h4 := norm_nonneg (Pᴴ * A)
  nlinarith [norm_nonneg P]

theorem norm_dotProduct_mulVec_star_le (A : Matrix n n ℂ) (x : n → ℂ) :
    ‖x ⬝ᵥ A *ᵥ star x‖ ≤ ‖A‖ * ∑ k, ‖x k‖ ^ 2 := by
  set y : EuclideanSpace ℂ n := WithLp.toLp 2 (star x) with hy
  have h := l2_opNorm_mulVec A y
  have h1 := norm_inner_le_norm (𝕜 := ℂ) y ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ y))
  have h2 : ‖y‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by simp [hy, EuclideanSpace.norm_sq_eq]
  have h3 : inner ℂ y ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ y)) = x ⬝ᵥ A *ᵥ star x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp [hy]
  rw [← h3, ← h2]
  refine h1.trans ?_
  nlinarith [norm_nonneg y]

theorem norm_diag_le_l2_opNorm (A : Matrix n n ℂ) (k : n) : ‖A k k‖ ≤ ‖A‖ := by
  have h := norm_dotProduct_mulVec_star_le A (Pi.single k 1)
  have h1 : ∑ l, ‖(Pi.single k 1 : n → ℂ) l‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single k] <;> simp +contextual [Pi.single_apply]
  rw [h1] at h
  simpa [← Pi.single_star] using h

theorem norm_trace_le_card_mul_l2_opNorm (A : Matrix n n ℂ) :
    ‖A.trace‖ ≤ Fintype.card n * ‖A‖ := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ‖A‖ fun k _ => norm_diag_le_l2_opNorm A k).trans ?_
  simp

end OpNorm

section LogDet

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem abs_log_norm_det_one_add_sub_re_trace_le {M : Matrix n n ℂ} {t : ℝ} (hM : ‖M‖ ≤ t)
    (ht : t < 1) :
    (1 + M).det ≠ 0 ∧ |Real.log ‖(1 + M).det‖ - M.trace.re| ≤
      Fintype.card n * t ^ 2 / (2 * (1 - t)) := by
  have hs : ∀ μ ∈ (1 + M).charpoly.roots, ‖μ - 1‖ ≤ t := by
    intro μ hμ
    have h1 : μ ∈ spectrum ℂ (1 + M) :=
      mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots hμ)
    have h2 : μ - 1 ∈ spectrum ℂ M := by
      rw [spectrum.mem_iff] at h1 ⊢
      convert h1 using 2
      rw [map_sub, map_one]
      abel
    have h3 := spectrum.norm_le_norm_mul_of_mem h2
    have h4 := l2_opNorm_one_le (n := n)
    nlinarith [norm_nonneg M]
  have hc : (1 + M).charpoly.roots.card = Fintype.card n := by
    rw [← charpoly_natDegree_eq_dim (1 + M)]
    exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have h := abs_log_norm_multisetProd_sub_le _ ht hs
  rw [← det_eq_prod_roots_charpoly, ← trace_eq_sum_roots_charpoly, hc, trace_add, trace_one,
    add_sub_cancel_left, ← mul_div_assoc] at h
  exact h

theorem abs_log_norm_det_sign_add_sub_re_trace_le_of_le {j : n → ℂ}
    (hj : ∀ k, j k = 1 ∨ j k = -1) {E : Matrix n n ℂ} {t : ℝ} (hE : ‖E‖ ≤ t) (ht : t < 1) :
    (diagonal j + E).det ≠ 0 ∧
      |Real.log ‖(diagonal j + E).det‖ - (diagonal j * E).trace.re| ≤
        Fintype.card n * t ^ 2 / (2 * (1 - t)) := by
  have hJ : diagonal j * diagonal j = (1 : Matrix n n ℂ) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext k
    rcases hj k with h | h <;> simp [h]
  have h1 : diagonal j + E = diagonal j * (1 + diagonal j * E) := by
    rw [mul_add, mul_one, ← mul_assoc, hJ, one_mul]
  have h2 : ‖(diagonal j).det‖ = 1 := by
    rw [det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun k _ => ?_
    rcases hj k with h | h <;> simp [h]
  have h3 : ‖diagonal j * E‖ ≤ t := by
    have := l2_opNorm_mul (diagonal j) E
    have := l2_opNorm_diagonal_sign_le hj
    nlinarith [norm_nonneg E]
  obtain ⟨h4, h5⟩ := abs_log_norm_det_one_add_sub_re_trace_le h3 ht
  rw [h1, det_mul, norm_mul, h2, one_mul]
  exact ⟨mul_ne_zero (norm_ne_zero_iff.1 (by rw [h2]; exact one_ne_zero)) h4, h5⟩

theorem abs_log_norm_det_sign_add_sub_re_trace_le {j : n → ℂ}
    (hj : ∀ k, j k = 1 ∨ j k = -1) {E : Matrix n n ℂ} (hE : ‖E‖ < 1) :
    (diagonal j + E).det ≠ 0 ∧
      |Real.log ‖(diagonal j + E).det‖ - (diagonal j * E).trace.re| ≤
        Fintype.card n * ‖E‖ ^ 2 / (2 * (1 - ‖E‖)) :=
  abs_log_norm_det_sign_add_sub_re_trace_le_of_le hj le_rfl hE

end LogDet

section Inertia

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
theorem dotProduct_diagonal_mulVec_star (d x : n → ℂ) :
    x ⬝ᵥ diagonal d *ᵥ star x = ∑ k, d k * ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

theorem le_re_dotProduct_diagonal_add_of_support {j : n → ℂ} (E : Matrix n n ℂ) {x : n → ℂ}
    (hx : ∀ k, x k ≠ 0 → j k = 1) :
    (1 - ‖E‖) * ∑ k, ‖x k‖ ^ 2 ≤ (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re := by
  have h1 : (x ⬝ᵥ diagonal j *ᵥ star x).re = ∑ k, ‖x k‖ ^ 2 := by
    rw [dotProduct_diagonal_mulVec_star, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : x k = 0
    · simp [h]
    · rw [hx k h, one_mul, Complex.ofReal_re]
  have h2 := norm_dotProduct_mulVec_star_le E x
  have h3 := abs_le.1 (Complex.abs_re_le_norm (x ⬝ᵥ E *ᵥ star x))
  rw [add_mulVec, dotProduct_add, Complex.add_re, h1]
  linarith [h3.1]

theorem sum_norm_sq_pos {x : n → ℂ} (hx : x ≠ 0) : 0 < ∑ k, ‖x k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  exact Finset.sum_pos' (fun _ _ => by positivity)
    ⟨k, Finset.mem_univ k, by have : x k ≠ 0 := hk; positivity⟩

theorem re_dotProduct_diagonal_add_pos_of_support {j : n → ℂ} {E : Matrix n n ℂ} (hE : ‖E‖ < 1)
    {x : n → ℂ} (hx0 : x ≠ 0) (hx : ∀ k, x k ≠ 0 → j k = 1) :
    0 < (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re :=
  (mul_pos (by linarith) (sum_norm_sq_pos hx0)).trans_le
    (le_re_dotProduct_diagonal_add_of_support E hx)

theorem re_dotProduct_diagonal_add_neg_of_support {j : n → ℂ} {E : Matrix n n ℂ} (hE : ‖E‖ < 1)
    {x : n → ℂ} (hx0 : x ≠ 0) (hx : ∀ k, x k ≠ 0 → j k = -1) :
    (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re < 0 := by
  have h := re_dotProduct_diagonal_add_pos_of_support (j := -j) (E := -E) (by rwa [norm_neg]) hx0
    fun k hk => by simp [hx k hk]
  have h1 : diagonal (-j) + -E = -(diagonal j + E) := by
    rw [neg_add, diagonal_neg]
    rfl
  rw [h1, neg_mulVec, dotProduct_neg, Complex.neg_re] at h
  linarith

theorem posDef_one_add {E : Matrix n n ℂ} (hE : E.IsHermitian) (hE1 : ‖E‖ < 1) :
    (1 + E).PosDef := by
  have hH : (1 + E).IsHermitian := isHermitian_one.add hE
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h := re_dotProduct_diagonal_add_pos_of_support (j := fun _ => 1) hE1
    (star_ne_zero.2 hx) fun _ _ => rfl
  rw [star_star, diagonal_one] at h
  rw [Complex.pos_iff]
  exact ⟨h, (hH.im_star_dotProduct_mulVec_self x).symm⟩

theorem posDef_submatrix_diagonal_add {j : n → ℂ} {E : Matrix n n ℂ} (hE : E.IsHermitian)
    (hE1 : ‖E‖ < 1) {e : m → n} (he : Function.Injective e) (hj : ∀ a, j (e a) = 1) :
    ((diagonal j + E).submatrix e e).PosDef := by
  have : (diagonal j + E).submatrix e e = 1 + E.submatrix e e := by
    ext a b
    simp [diagonal_apply, one_apply, he.eq_iff, hj]
  rw [this]
  exact posDef_one_add (hE.submatrix e) ((l2_opNorm_submatrix_le E he).trans_lt hE1)

theorem posDef_neg_submatrix_diagonal_add {j : n → ℂ} {E : Matrix n n ℂ} (hE : E.IsHermitian)
    (hE1 : ‖E‖ < 1) {e : m → n} (he : Function.Injective e) (hj : ∀ a, j (e a) = -1) :
    (-(diagonal j + E).submatrix e e).PosDef := by
  have h := posDef_submatrix_diagonal_add (j := -j) hE.neg (by rwa [norm_neg]) he
    fun a => by simp [hj]
  convert h using 1
  ext a b
  by_cases hab : e a = e b <;> simp [diagonal_apply, hab, add_comm]

omit [DecidableEq n] in

theorem finrank_le_card_of_eq_zero (S : Finset n) (W : Submodule ℂ (n → ℂ))
    (h : ∀ x ∈ W, (∀ k ∈ S, x k = 0) → x = 0) : Module.finrank ℂ W ≤ S.card := by
  let f : W →ₗ[ℂ] (S → ℂ) := (LinearMap.funLeft ℂ ℂ (Subtype.val : S → n)).comp W.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (h x x.2 fun k hk => congrFun hx ⟨k, hk⟩)
  simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem isGreatest_finrank_pos_sign_add {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1)
    {E : Matrix n n ℂ} (hE : ‖E‖ < 1) :
    IsGreatest {d : ℕ | ∃ W : Submodule ℂ (n → ℂ), Module.finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → 0 < (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re}
      (Finset.univ.filter fun k => j k = 1).card := by
  refine ⟨⟨Pi.spanSubset ℂ {k | j k = 1}, ?_, fun x hx hx0 => ?_⟩, ?_⟩
  · rw [Pi.dim_spanSubset, Set.ncard_eq_toFinset_card']
    simp
  · refine re_dotProduct_diagonal_add_pos_of_support hE hx0 fun k hk => ?_
    by_contra h
    exact hk (Pi.mem_spanSubset_iff.1 hx k h)
  · rintro d ⟨W, rfl, hW⟩
    refine finrank_le_card_of_eq_zero _ W fun x hx h0 => ?_
    by_contra hx0
    refine (hW x hx hx0).not_gt (re_dotProduct_diagonal_add_neg_of_support hE hx0 fun k hk => ?_)
    exact (hj k).resolve_left fun h => hk (h0 k (by simpa using h))

theorem isGreatest_finrank_neg_sign_add {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1)
    {E : Matrix n n ℂ} (hE : ‖E‖ < 1) :
    IsGreatest {d : ℕ | ∃ W : Submodule ℂ (n → ℂ), Module.finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re < 0}
      (Finset.univ.filter fun k => j k = -1).card := by
  have h := isGreatest_finrank_pos_sign_add (j := -j) (E := -E)
    (fun k => by rcases hj k with h | h <;> simp [h]) (by rwa [norm_neg])
  have h1 : diagonal (-j) + -E = -(diagonal j + E) := by
    rw [neg_add, diagonal_neg]
    rfl
  simpa only [h1, neg_mulVec, dotProduct_neg, Complex.neg_re, Left.neg_pos_iff, Pi.neg_apply,
    neg_eq_iff_eq_neg] using h

theorem card_le_card_pos_of_posDef (d : n → ℝ) (Q : Matrix n m ℂ)
    (h : (Qᴴ * diagonal (fun k => (d k : ℂ)) * Q).PosDef) :
    Fintype.card m ≤ (Finset.univ.filter fun k => 0 < d k).card := by
  set S := Finset.univ.filter fun k => 0 < d k with hS
  let f : (m → ℂ) →ₗ[ℂ] (S → ℂ) := (LinearMap.funLeft ℂ ℂ (Subtype.val : S → n)).comp Q.mulVecLin
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have h1 := (Complex.pos_iff.1 (h.dotProduct_mulVec_pos hx0)).1
    have h2 : star x ⬝ᵥ (Qᴴ * diagonal (fun k => (d k : ℂ)) * Q) *ᵥ x =
        star (Q *ᵥ x) ⬝ᵥ diagonal (fun k => (d k : ℂ)) *ᵥ star (star (Q *ᵥ x)) := by
      rw [star_star, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
    rw [h2, dotProduct_diagonal_mulVec_star, Complex.re_sum] at h1
    refine h1.not_ge (Finset.sum_nonpos fun k _ => ?_)
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    by_cases hk : 0 < d k
    · have : (Q *ᵥ x) k = 0 := congrFun hx ⟨k, by simpa [hS] using hk⟩
      simp [this]
    · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hk) (by positivity)
  simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem submatrix_eq_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) (e : m → n) :
    ∃ Q : Matrix n m ℂ,
      A.submatrix e e = Qᴴ * diagonal (fun k => (hA.eigenvalues k : ℂ)) * Q := by
  refine ⟨(star (hA.eigenvectorUnitary : Matrix n n ℂ)).submatrix id e, ?_⟩
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [submatrix_mul _ _ e id e Function.bijective_id,
    submatrix_mul _ _ e id id Function.bijective_id]
  simp [star_eq_conjTranspose, Function.comp_def]

theorem card_eigenvalues_sign_add {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1)
    {E : Matrix n n ℂ} (hE : ‖E‖ < 1) (hH : (diagonal j + E).IsHermitian) :
    (Finset.univ.filter fun k => 0 < hH.eigenvalues k).card =
        (Finset.univ.filter fun k => j k = 1).card ∧
      (Finset.univ.filter fun k => hH.eigenvalues k < 0).card =
        (Finset.univ.filter fun k => j k = -1).card := by
  have hJ : (diagonal j).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by
      ext k
      rcases hj k with h | h <;> simp [h])
  have hEH : E.IsHermitian := by simpa using hH.sub hJ
  have hp : (Finset.univ.filter fun k => j k = 1).card ≤
      (Finset.univ.filter fun k => 0 < hH.eigenvalues k).card := by
    obtain ⟨Q, hQ⟩ := submatrix_eq_eigenvalues hH (Subtype.val : {k // j k = 1} → n)
    have h := posDef_submatrix_diagonal_add hEH hE
      (Subtype.val_injective (p := fun k => j k = 1)) fun a => a.2
    rw [hQ] at h
    simpa [Fintype.card_subtype] using card_le_card_pos_of_posDef _ Q h
  have hq : (Finset.univ.filter fun k => j k = -1).card ≤
      (Finset.univ.filter fun k => hH.eigenvalues k < 0).card := by
    obtain ⟨Q, hQ⟩ := submatrix_eq_eigenvalues hH (Subtype.val : {k // j k = -1} → n)
    have h := posDef_neg_submatrix_diagonal_add hEH hE
      (Subtype.val_injective (p := fun k => j k = -1)) fun a => a.2
    rw [hQ, ← Matrix.neg_mul, ← Matrix.mul_neg, diagonal_neg] at h
    have h' := card_le_card_pos_of_posDef (fun k => -hH.eigenvalues k) Q (by simpa using h)
    simpa [Fintype.card_subtype] using h'
  have h1 : (Finset.univ.filter fun k => 0 < hH.eigenvalues k).card +
      (Finset.univ.filter fun k => hH.eigenvalues k < 0).card ≤ Fintype.card n := by
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_univ _
    · exact Finset.disjoint_filter.2 fun k _ h => h.le.not_gt
  have h2 : Fintype.card n ≤ (Finset.univ.filter fun k => j k = 1).card +
      (Finset.univ.filter fun k => j k = -1).card := by
    refine le_trans (Finset.card_le_card fun k _ => ?_) (Finset.card_union_le _ _)
    simpa using hj k
  omega

end Inertia

section Exp

open NormedSpace

theorem norm_exp_sub_one_sub_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (x : A) : ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  have h1 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have h2 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul, zero_add,
    ← sub_sub] at h1 h2
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun k => ?_
  rw [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  gcongr
  exact norm_pow_le' x (by omega)

theorem norm_exp_sub_one_sub_le_of_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] {x : A} {ρ : ℝ} (hx : ‖x‖ ≤ ρ) (hρ : ρ ≤ 1 / 10) :
    ‖exp x - 1 - x‖ ≤ 0.53 * ρ ^ 2 := by
  have h0 := norm_nonneg x
  have h := Real.exp_bound' h0 (by linarith) (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h
  have h1 := norm_exp_sub_one_sub_le x
  have h2 : ‖x‖ ^ 2 ≤ ρ ^ 2 := by gcongr
  have h3 : ‖x‖ ^ 3 ≤ ‖x‖ ^ 2 / 10 := by nlinarith [sq_nonneg ‖x‖]
  nlinarith

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem transpose_mul_diagonal_mul_map_star_apply (j : n → ℂ) (g : Matrix n m ℂ) (k l : m) :
    (gᵀ * diagonal j * g.map star) k l = ∑ a, j a * (g a k * star (g a l)) := by
  rw [mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_diagonal, transpose_apply, map_apply]
  ring

omit [Fintype m] [DecidableEq m] in

theorem conjTranspose_mul_diagonal_mul_eq_transpose (j : n → ℂ) (g : Matrix n m ℂ) :
    gᴴ * diagonal j * g = (gᵀ * diagonal j * g.map star)ᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  rfl

omit [Fintype m] [DecidableEq m] in
theorem isHermitian_transpose_mul_sign_mul_map_star {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1)
    (g : Matrix n m ℂ) : (gᵀ * diagonal j * g.map star).IsHermitian := by
  have hJ : (diagonal j).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by
      ext k
      rcases hj k with h | h <;> simp [h])
  have : gᵀ = (g.map star)ᴴ := by ext; simp
  rw [this]
  exact isHermitian_conjTranspose_mul_mul _ hJ

theorem l2_opNorm_gram_exp_sub_sub_le {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1)
    {u : Matrix n n ℂ} {ρ : ℝ} (hu : ‖u‖ ≤ ρ) (hρ : ρ ≤ 1 / 10) :
    ‖(exp u)ᵀ * diagonal j * (exp u).map star - diagonal j -
      (uᵀ * diagonal j + diagonal j * u.map star)‖ ≤ 2.2 * ρ ^ 2 := by
  have hv := norm_exp_sub_one_sub_le_of_le hu hρ
  have hρ0 : 0 ≤ ρ := (norm_nonneg u).trans hu
  obtain ⟨v, hvdef⟩ : ∃ v, v = exp u - 1 - u := ⟨_, rfl⟩
  rw [← hvdef] at hv
  have hexp : exp u = 1 + (u + v) := by rw [hvdef]; abel
  have hJ := l2_opNorm_diagonal_sign_le hj
  have hX : ‖u + v‖ ≤ 1.053 * ρ := by
    refine (norm_add_le u v).trans ?_
    nlinarith
  have hstar : (1 + (u + v) : Matrix n n ℂ).map star = 1 + (u.map star + v.map star) := by
    ext a b
    by_cases h : a = b <;> simp [one_apply, h]
  have hstar' : (u + v : Matrix n n ℂ).map star = u.map star + v.map star := by
    ext a b
    simp
  have heq : (exp u)ᵀ * diagonal j * (exp u).map star - diagonal j -
      (uᵀ * diagonal j + diagonal j * u.map star) =
      vᵀ * diagonal j + diagonal j * v.map star + (u + v)ᵀ * diagonal j * (u + v).map star := by
    rw [hexp, hstar, hstar']
    simp only [transpose_add, transpose_one]
    noncomm_ring
  have hl : ∀ A : Matrix n n ℂ, ‖Aᵀ * diagonal j‖ ≤ ‖A‖ := fun A => by
    have := l2_opNorm_mul Aᵀ (diagonal j)
    rw [l2_opNorm_transpose] at this
    nlinarith [norm_nonneg A]
  have hr : ‖diagonal j * v.map star‖ ≤ ‖v‖ := by
    have := l2_opNorm_mul (diagonal j) (v.map star)
    rw [l2_opNorm_map_star] at this
    nlinarith [norm_nonneg v]
  have h3 : ‖(u + v)ᵀ * diagonal j * (u + v).map star‖ ≤ (1.053 * ρ) * (1.053 * ρ) := by
    refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_map_star]
    exact mul_le_mul ((hl _).trans hX) hX (norm_nonneg _) (by positivity)
  rw [heq]
  refine norm_add₃_le.trans ?_
  nlinarith [hl v, sq_nonneg ρ]

theorem l2_opNorm_gram_exp_sub_le {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1)
    {u : Matrix n n ℂ} {ρ : ℝ} (hu : ‖u‖ ≤ ρ) (hρ : ρ ≤ 1 / 10) :
    ‖(exp u)ᵀ * diagonal j * (exp u).map star - diagonal j‖ ≤ 2.3 * ρ := by
  have h := l2_opNorm_gram_exp_sub_sub_le hj hu hρ
  have hρ0 : 0 ≤ ρ := (norm_nonneg u).trans hu
  have hJ := l2_opNorm_diagonal_sign_le hj
  have hl : ‖uᵀ * diagonal j‖ ≤ ‖u‖ := by
    have := l2_opNorm_mul uᵀ (diagonal j)
    rw [l2_opNorm_transpose] at this
    nlinarith [norm_nonneg u]
  have hr : ‖diagonal j * u.map star‖ ≤ ‖u‖ := by
    have := l2_opNorm_mul (diagonal j) (u.map star)
    rw [l2_opNorm_map_star] at this
    nlinarith [norm_nonneg u]
  have h1 := norm_add_le (uᵀ * diagonal j) (diagonal j * u.map star)
  have h2 := norm_le_insert' ((exp u)ᵀ * diagonal j * (exp u).map star - diagonal j)
    (uᵀ * diagonal j + diagonal j * u.map star)
  nlinarith

theorem l2_opNorm_conjTranspose_exp_mul_sign_mul_exp_sub_le {j : n → ℂ}
    (hj : ∀ k, j k = 1 ∨ j k = -1) {u : Matrix n n ℂ} {ρ : ℝ} (hu : ‖u‖ ≤ ρ) (hρ : ρ ≤ 1 / 10) :
    ‖(exp u)ᴴ * diagonal j * exp u - diagonal j‖ ≤ 2.3 * ρ := by
  rw [conjTranspose_mul_diagonal_mul_eq_transpose, ← l2_opNorm_transpose, transpose_sub,
    transpose_transpose, diagonal_transpose]
  exact l2_opNorm_gram_exp_sub_le hj hu hρ

omit [Fintype m] [Fintype n] in
theorem submatrix_eq_diagonal_add (j : n → ℂ) (G : Matrix n n ℂ) {e : m → n}
    (he : Function.Injective e) :
    G.submatrix e e = diagonal (j ∘ e) + (G - diagonal j).submatrix e e := by
  ext a b
  simp [diagonal_apply, he.eq_iff]

theorem abs_log_norm_det_gram_exp_submatrix_le {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1)
    {u : Matrix n n ℂ} (hu0 : ∀ k, u k k = 0) {ρ : ℝ} (hu : ‖u‖ ≤ ρ) (hρ : ρ ≤ 1 / 10)
    {e : m → n} (he : Function.Injective e) :
    (((exp u)ᵀ * diagonal j * (exp u).map star).submatrix e e).det ≠ 0 ∧
      |Real.log ‖(((exp u)ᵀ * diagonal j * (exp u).map star).submatrix e e).det‖| ≤
        5.7 * Fintype.card m * ρ ^ 2 := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg u).trans hu
  have h1 := l2_opNorm_gram_exp_sub_le hj hu hρ
  have h2 := l2_opNorm_gram_exp_sub_sub_le hj hu hρ
  set G := (exp u)ᵀ * diagonal j * (exp u).map star with hG
  have hj' : ∀ a, (j ∘ e) a = 1 ∨ (j ∘ e) a = -1 := fun a => hj (e a)
  obtain ⟨h3, h4⟩ := abs_log_norm_det_sign_add_sub_re_trace_le_of_le hj'
    ((l2_opNorm_submatrix_le _ he).trans h1) (by linarith)
  rw [submatrix_eq_diagonal_add j G he]
  refine ⟨h3, ?_⟩
  have h5 : (diagonal (j ∘ e) * (G - diagonal j).submatrix e e).trace =
      (diagonal (j ∘ e) * (G - diagonal j -
        (uᵀ * diagonal j + diagonal j * u.map star)).submatrix e e).trace := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hu0]
  have h6 : ‖diagonal (j ∘ e) * (G - diagonal j -
        (uᵀ * diagonal j + diagonal j * u.map star)).submatrix e e‖ ≤ 2.2 * ρ ^ 2 := by
    refine (l2_opNorm_mul _ _).trans ?_
    rw [← one_mul (2.2 * ρ ^ 2)]
    exact mul_le_mul (l2_opNorm_diagonal_sign_le hj') ((l2_opNorm_submatrix_le _ he).trans h2)
      (norm_nonneg _) zero_le_one
  have h7 : |(diagonal (j ∘ e) * (G - diagonal j).submatrix e e).trace.re| ≤
      Fintype.card m * (2.2 * ρ ^ 2) := by
    rw [h5]
    refine (Complex.abs_re_le_norm _).trans ((norm_trace_le_card_mul_l2_opNorm _).trans ?_)
    gcongr
  have h8 : (Fintype.card m : ℝ) * (2.3 * ρ) ^ 2 / (2 * (1 - 2.3 * ρ)) ≤
      Fintype.card m * (3.5 * ρ ^ 2) := by
    rw [mul_div_assoc]
    gcongr
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ρ, mul_le_mul_of_nonneg_left hρ (sq_nonneg ρ)]
  have h9 := abs_sub_abs_le_abs_sub
    (Real.log ‖(diagonal (j ∘ e) + (G - diagonal j).submatrix e e).det‖)
    (diagonal (j ∘ e) * (G - diagonal j).submatrix e e).trace.re
  linarith

theorem signature_submatrix_of_norm_sub_sign_lt_one {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1)
    {G : Matrix n n ℂ} (hG : G.IsHermitian) (h : ‖G - diagonal j‖ < 1)
    {e : m → n} (he : Function.Injective e) :
    IsGreatest {d : ℕ | ∃ W : Submodule ℂ (m → ℂ), Module.finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → 0 < (x ⬝ᵥ G.submatrix e e *ᵥ star x).re}
      (Finset.univ.filter fun a => j (e a) = 1).card ∧
    IsGreatest {d : ℕ | ∃ W : Submodule ℂ (m → ℂ), Module.finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → (x ⬝ᵥ G.submatrix e e *ᵥ star x).re < 0}
      (Finset.univ.filter fun a => j (e a) = -1).card ∧
    (Finset.univ.filter fun a => 0 < (hG.submatrix e).eigenvalues a).card =
      (Finset.univ.filter fun a => j (e a) = 1).card ∧
    (Finset.univ.filter fun a => (hG.submatrix e).eigenvalues a < 0).card =
      (Finset.univ.filter fun a => j (e a) = -1).card ∧
    ((∀ a, j (e a) = 1) → (G.submatrix e e).PosDef) ∧
    ((∀ a, j (e a) = -1) → (-G.submatrix e e).PosDef) := by
  have hj' : ∀ a, (j ∘ e) a = 1 ∨ (j ∘ e) a = -1 := fun a => hj (e a)
  have h1 := (l2_opNorm_submatrix_le _ he).trans_lt h
  have hJ : (diagonal j).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by
      ext k
      rcases hj k with h | h <;> simp [h])
  have h2 := fun h' => posDef_submatrix_diagonal_add (j := j) (hG.sub hJ) h he h'
  have h3 := fun h' => posDef_neg_submatrix_diagonal_add (j := j) (hG.sub hJ) h he h'
  rw [add_sub_cancel] at h2 h3
  have h4 := isGreatest_finrank_pos_sign_add hj' h1
  have h5 := isGreatest_finrank_neg_sign_add hj' h1
  have h6 := card_eigenvalues_sign_add hj' h1
  rw [← submatrix_eq_diagonal_add j G he] at h4 h5 h6
  exact ⟨h4, h5, (h6 _).1, (h6 _).2, h2, h3⟩

theorem gram_exp_submatrix_logDet_and_signature {j : n → ℂ} (hj : ∀ k, j k = 1 ∨ j k = -1)
    {u : Matrix n n ℂ} (hu0 : ∀ k, u k k = 0) {ρ : ℝ} (hu : ‖u‖ ≤ ρ) (hρ : ρ ≤ 1 / 10)
    {e : m → n} (he : Function.Injective e) {B : Matrix m m ℂ}
    (hB : B = ((exp u)ᵀ * diagonal j * (exp u).map star).submatrix e e) :
    B.det ≠ 0 ∧ |Real.log ‖B.det‖| ≤ 11 * Fintype.card n * ρ ^ 2 ∧
    IsGreatest {d : ℕ | ∃ W : Submodule ℂ (m → ℂ), Module.finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → 0 < (x ⬝ᵥ B *ᵥ star x).re}
      (Finset.univ.filter fun a => j (e a) = 1).card ∧
    IsGreatest {d : ℕ | ∃ W : Submodule ℂ (m → ℂ), Module.finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → (x ⬝ᵥ B *ᵥ star x).re < 0}
      (Finset.univ.filter fun a => j (e a) = -1).card ∧
    (∃ hH : B.IsHermitian,
      (Finset.univ.filter fun a => 0 < hH.eigenvalues a).card =
        (Finset.univ.filter fun a => j (e a) = 1).card ∧
      (Finset.univ.filter fun a => hH.eigenvalues a < 0).card =
        (Finset.univ.filter fun a => j (e a) = -1).card) ∧
    ((∀ a, j (e a) = 1) → B.PosDef) ∧ ((∀ a, j (e a) = -1) → (-B).PosDef) := by
  subst hB
  obtain ⟨h1, h2⟩ := abs_log_norm_det_gram_exp_submatrix_le hj hu0 hu hρ he
  obtain ⟨h3, h4, h5, h6, h7, h8⟩ := signature_submatrix_of_norm_sub_sign_lt_one hj
    (isHermitian_transpose_mul_sign_mul_map_star hj (exp u))
    ((l2_opNorm_gram_exp_sub_le hj hu hρ).trans_lt (by linarith)) he
  refine ⟨h1, h2.trans ?_, h3, h4, ⟨_, h5, h6⟩, h7, h8⟩
  have : (Fintype.card m : ℝ) ≤ Fintype.card n := by
    exact_mod_cast Fintype.card_le_of_injective e he
  gcongr
  norm_num

theorem conjTranspose_exp_mul_sign_mul_exp_submatrix_logDet_and_signature {j : n → ℂ}
    (hj : ∀ k, j k = 1 ∨ j k = -1)
    {u : Matrix n n ℂ} (hu0 : ∀ k, u k k = 0) {ρ : ℝ} (hu : ‖u‖ ≤ ρ) (hρ : ρ ≤ 1 / 10)
    {e : m → n} (he : Function.Injective e) {B : Matrix m m ℂ}
    (hB : B = ((exp u)ᴴ * diagonal j * exp u).submatrix e e) :
    B.det ≠ 0 ∧ |Real.log ‖B.det‖| ≤ 11 * Fintype.card n * ρ ^ 2 ∧
    (∃ hH : B.IsHermitian,
      (Finset.univ.filter fun a => 0 < hH.eigenvalues a).card =
        (Finset.univ.filter fun a => j (e a) = 1).card ∧
      (Finset.univ.filter fun a => hH.eigenvalues a < 0).card =
        (Finset.univ.filter fun a => j (e a) = -1).card) ∧
    ((∀ a, j (e a) = 1) → B.PosDef) ∧ ((∀ a, j (e a) = -1) → (-B).PosDef) := by
  subst hB
  obtain ⟨h1, h2, -⟩ := gram_exp_submatrix_logDet_and_signature hj hu0 hu hρ he rfl
  have hH : ((exp u)ᴴ * diagonal j * exp u).IsHermitian := by
    rw [conjTranspose_mul_diagonal_mul_eq_transpose]
    exact (isHermitian_transpose_mul_sign_mul_map_star hj _).transpose
  obtain ⟨-, -, h5, h6, h7, h8⟩ := signature_submatrix_of_norm_sub_sign_lt_one hj hH
    ((l2_opNorm_conjTranspose_exp_mul_sign_mul_exp_sub_le hj hu hρ).trans_lt (by linarith)) he
  have hd : (((exp u)ᴴ * diagonal j * exp u).submatrix e e).det =
      (((exp u)ᵀ * diagonal j * (exp u).map star).submatrix e e).det := by
    rw [conjTranspose_mul_diagonal_mul_eq_transpose, ← transpose_submatrix, det_transpose]
  rw [hd]
  exact ⟨h1, h2, ⟨_, h5, h6⟩, h7, h8⟩

theorem gram_exp_leadingBlock_logDet_and_signature {r i : ℕ} (hi : i ≤ r) {j : Fin r → ℂ}
    (hj : ∀ k, j k = 1 ∨ j k = -1) {u : Matrix (Fin r) (Fin r) ℂ}
    (hu0 : (∀ k l, k ≤ l → u k l = 0) ∨ ∀ k l, l ≤ k → u k l = 0)
    {ρ : ℝ} (hu : ‖u‖ ≤ ρ) (hρ : ρ ≤ 1 / 10) {B : Matrix (Fin i) (Fin i) ℂ}
    (hB : B = ((exp u)ᵀ * diagonal j * (exp u).map star).submatrix
      (Fin.castLE hi) (Fin.castLE hi)) :
    B.det ≠ 0 ∧ |Real.log ‖B.det‖| ≤ 11 * r * ρ ^ 2 ∧
    IsGreatest {d : ℕ | ∃ W : Submodule ℂ (Fin i → ℂ), Module.finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → 0 < (x ⬝ᵥ B *ᵥ star x).re}
      (Finset.univ.filter fun a => j (Fin.castLE hi a) = 1).card ∧
    IsGreatest {d : ℕ | ∃ W : Submodule ℂ (Fin i → ℂ), Module.finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → (x ⬝ᵥ B *ᵥ star x).re < 0}
      (Finset.univ.filter fun a => j (Fin.castLE hi a) = -1).card ∧
    (∃ hH : B.IsHermitian,
      (Finset.univ.filter fun a => 0 < hH.eigenvalues a).card =
        (Finset.univ.filter fun a => j (Fin.castLE hi a) = 1).card ∧
      (Finset.univ.filter fun a => hH.eigenvalues a < 0).card =
        (Finset.univ.filter fun a => j (Fin.castLE hi a) = -1).card) ∧
    ((∀ a, j (Fin.castLE hi a) = 1) → B.PosDef) ∧
    ((∀ a, j (Fin.castLE hi a) = -1) → (-B).PosDef) := by
  have h := gram_exp_submatrix_logDet_and_signature hj
    (fun k => hu0.elim (fun h => h k k le_rfl) fun h => h k k le_rfl) hu hρ
    (Fin.castLE_injective hi) hB
  rwa [Fintype.card_fin] at h

end Exp

end GlobalTheory
