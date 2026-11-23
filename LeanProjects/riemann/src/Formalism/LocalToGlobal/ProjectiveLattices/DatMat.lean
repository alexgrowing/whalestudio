import Mathlib

noncomputable section

namespace Formalism.L2.Pj.DatLin

open Matrix Complex

section Mat

variable {m : Type} [Fintype m] [DecidableEq m]

theorem star_mulVec_dot (A B : Matrix m m ℂ) (u w : m → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (B *ᵥ w) = star u ⬝ᵥ ((Aᴴ * B) *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem star_dot_self_eq (w : m → ℂ) : star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, Complex.star_def]

theorem sum_normSq_pos {w : m → ℂ} (hw : w ≠ 0) : 0 < ∑ i, Complex.normSq (w i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩

theorem cplx_str_core (H P Q J : Matrix m m ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hJ2 : J * J = 1) (hJh : Jᴴ = J) (hH : Pᴴ * H * P = J) :
    let K := P * (Complex.I • J) * Q
    (K * K = -1) ∧ (Kᴴ * H * K = H) ∧ (Kᴴ * H = (-Complex.I) • (Qᴴ * Q)) ∧
      K.trace = Complex.I * J.trace := by
  dsimp only
  have hQP' : ∀ X : Matrix m m ℂ, Q * (P * X) = X := fun X => by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hJ2' : ∀ X : Matrix m m ℂ, J * (J * X) = X := fun X => by rw [← Matrix.mul_assoc, hJ2, Matrix.one_mul]
  have hPQh' : ∀ X : Matrix m m ℂ, Pᴴ * (Qᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one, Matrix.one_mul]

  have hH' : H = Qᴴ * (J * Q) := by
    have hq : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
    calc H = (Qᴴ * Pᴴ) * H * (P * Q) := by rw [hq, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = Qᴴ * ((Pᴴ * H * P) * Q) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (J * Q) := by rw [hH]
  have hsI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQ, Complex.I_mul_I,
      neg_smul, one_smul]
  · rw [hH']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hJh, hsI, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQh']
    rw [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  · rw [hH']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hJh, hsI, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQh']
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]

theorem exists_cplx_str {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (p q : ℕ)
    (e : n ≃ Fin p ⊕ Fin q) (P : GL (Fin p ⊕ Fin q) ℂ)
    (hP : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ))ᵀ * H.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Matrix.fromBlocks 1 0 0 (-1)) :
    ∃ K : Matrix n n ℂ, (∀ u, K *ᵥ (K *ᵥ u) = -u) ∧
      (∀ u w, star (K *ᵥ u) ⬝ᵥ (H *ᵥ (K *ᵥ w)) = star u ⬝ᵥ (H *ᵥ w)) ∧
      (∀ u : n → ℂ, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (H *ᵥ u) = -(Complex.I * ρ)) ∧
      K.trace = Complex.I * ((p : ℂ) - q) := by
  set P0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hP0
  set Q0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
    ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQ0
  set J0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hJ0
  have hPh : (P0.map (starRingEnd ℂ))ᵀ = P0ᴴ := rfl
  rw [hPh] at hP
  have hPQ0 : P0 * Q0 = 1 := P.mul_inv
  have hQP0 : Q0 * P0 = 1 := P.inv_mul
  have hJJ0 : J0 * J0 = 1 := by
    simp [hJ0, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  set Pn := P0.submatrix e e
  set Qn := Q0.submatrix e e
  set Jn := J0.submatrix e e
  have hPQ : Pn * Qn = 1 := by rw [Matrix.submatrix_mul_equiv, hPQ0, Matrix.submatrix_one_equiv]
  have hQP : Qn * Pn = 1 := by rw [Matrix.submatrix_mul_equiv, hQP0, Matrix.submatrix_one_equiv]
  have hJ2 : Jn * Jn = 1 := by rw [Matrix.submatrix_mul_equiv, hJJ0, Matrix.submatrix_one_equiv]
  have hJh : Jnᴴ = Jn := by
    simp [Jn, hJ0, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  have hH : Pnᴴ * H * Pn = Jn := by
    have hH0 : H = (H.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hH0, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hP]
  obtain ⟨h1, h2, h3, h4⟩ := cplx_str_core H Pn Qn Jn hPQ hQP hJ2 hJh hH
  refine ⟨Pn * (Complex.I • Jn) * Qn, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [Matrix.mulVec_mulVec, h1, Matrix.neg_mulVec, Matrix.one_mulVec]
  · intro u w
    rw [Matrix.mulVec_mulVec, star_mulVec_dot, ← Matrix.mul_assoc, h2]
  · intro u hu
    refine ⟨∑ i, Complex.normSq ((Qn *ᵥ u) i), sum_normSq_pos ?_, ?_⟩
    · intro h0
      apply hu
      have := congrArg (Pn *ᵥ ·) h0
      simpa [Matrix.mulVec_mulVec, hPQ] using this
    · rw [star_mulVec_dot, h3, Matrix.smul_mulVec, dotProduct_smul, ← star_mulVec_dot, star_dot_self_eq,
        smul_eq_mul, neg_mul]
  · rw [h4]
    congr 1
    have ht : Jn.trace = J0.trace := by
      simp only [Matrix.trace, Matrix.diag, Jn, Matrix.submatrix_apply]
      exact Equiv.sum_comp e (fun i => J0 i i)
    rw [ht, hJ0]
    simp [Matrix.trace, Fintype.sum_sum_type, sub_eq_add_neg]

end Mat

section GlobalTheory

variable {ι n : Type} [Fintype ι] [Fintype n]

def blk (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℝ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by
    ext τ i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Matrix.mulVec_smul]
    rfl

theorem blk_apply (N : ι → Matrix n n ℂ) (u : ι → n → ℂ) (τ : ι) : blk N u τ = N τ *ᵥ u τ := rfl

theorem blk_comp (N N' : ι → Matrix n n ℂ) : blk N ∘ₗ blk N' = blk (fun τ => N τ * N' τ) := by
  apply LinearMap.ext
  intro u
  funext τ
  simp only [LinearMap.comp_apply, blk_apply, Matrix.mulVec_mulVec]

def blkC (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℂ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by ext τ : 1; simp [Matrix.mulVec_smul]

theorem blk_eq_restrict (N : ι → Matrix n n ℂ) : blk N = (blkC N).restrictScalars ℝ := rfl

theorem trace_restrict_complex {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] [Module.Free ℂ M] [Module.Finite ℂ M] (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℝ M (f.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ M f).re := by
  classical
  let c := Module.Free.chooseBasis ℂ M
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower c), LinearMap.trace_eq_matrix_trace ℂ c]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    Fintype.sum_prod_type, LinearMap.restrictScalars_apply, LinearMap.map_smul, map_smul, Finsupp.smul_apply,
    smul_eq_mul, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, Fin.sum_univ_two]
  simp [Complex.re_sum, Finset.mul_sum, Finset.sum_add_distrib, two_mul]

theorem trace_blkC [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℂ _ (blkC N) = ∑ τ, (N τ).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _ : ι => Pi.basisFun ℂ n)]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_sigma, blkC, Matrix.mulVec_single_one]

theorem trace_blk [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℝ _ (blk N) = ∑ τ, 2 * (N τ).trace.re := by
  rw [blk_eq_restrict, trace_restrict_complex, trace_blkC, Complex.re_sum, Finset.mul_sum]

end GlobalTheory

end Formalism.L2.Pj.DatLin
