import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoCharOfMulPolyDivPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LaurentPolyEvalOfLaurentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LaurentMonomialOfMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
open Matrix GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtHW

def diagGLOfNeZero {n : ℕ} (d : Fin n → ℂ) (h : ∀ i, d i ≠ 0) : GL (Fin n) ℂ :=
  ⟨diagonal d, diagonal d⁻¹, by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp [h i],
   by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp [h i]⟩

theorem diagGLOfNeZero_val {n : ℕ} (d : Fin n → ℂ) (h : ∀ i, d i ≠ 0) :
    (diagGLOfNeZero d h).val = diagonal d := rfl

theorem diagGLOfNeZero_inv_val {n : ℕ} (d : Fin n → ℂ) (h : ∀ i, d i ≠ 0) :
    ((diagGLOfNeZero d h)⁻¹).val = diagonal d⁻¹ := rfl

theorem diagGLOfNeZero_mul {n : ℕ} (s t : Fin n → ℂ) (hs : ∀ i, s i ≠ 0) (ht : ∀ i, t i ≠ 0) :
    diagGLOfNeZero (s * t) (fun i => mul_ne_zero (hs i) (ht i)) = diagGLOfNeZero s hs * diagGLOfNeZero t ht := by
  ext1; simp [diagGLOfNeZero_val, diagonal_mul_diagonal]

theorem exists_isWt_of_isPolyRep : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ μ : Fin n → ℤ, IsWt Φ μ := by
  intro n ι _ _ _ Φ hΦ
  classical
  let T : {D : GL (Fin n) ℂ // D.val.IsDiag} → (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
    fun D => Matrix.toLin' (Φ D.1)
  have hcomm : ∀ D D' : {D : GL (Fin n) ℂ // D.val.IsDiag}, D.1 * D'.1 = D'.1 * D.1 := by
    intro D D'
    ext1
    have h1 := D.2.diagonal_diag
    have h2 := D'.2.diagonal_diag
    rw [Units.val_mul, Units.val_mul, ← h1, ← h2, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i; ring
  have hT : ∀ i j x, T i (T j x) = T j (T i x) := by
    intro i j x
    simp only [T, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hΦ.mul, ← hΦ.mul, hcomm]
  obtain ⟨v, -, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_mem T hT ⊤ top_ne_bot
    (fun _ _ _ => Submodule.mem_top)
  choose c hc using hv
  have hc' : ∀ (D : GL (Fin n) ℂ) (hD : D.val.IsDiag), Φ D *ᵥ v = c ⟨D, hD⟩ • v := by
    intro D hD
    simpa [T] using hc ⟨D, hD⟩
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  have cancel : ∀ x y : ℂ, x • v = y • v → x = y := by
    intro x y h
    have := congrFun h a
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ ha this
  let χ : (Fin n → ℂ) → ℂ := fun d =>
    if h : ∀ i, d i ≠ 0 then (Φ (diagGLOfNeZero d h) *ᵥ v) a / v a else 0
  have hχ : ∀ d (h : ∀ i, d i ≠ 0), Φ (diagGLOfNeZero d h) *ᵥ v = χ d • v := by
    intro d h
    have e := hc' (diagGLOfNeZero d h) (by rw [diagGLOfNeZero_val]; exact isDiag_diagonal d)
    rw [e]
    congr 1
    simp only [χ, dif_pos h, e, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ ha]
  have h1 : χ 1 = 1 := by
    have e : diagGLOfNeZero (1 : Fin n → ℂ) (fun _ => one_ne_zero) = 1 := by
      ext1; simp [diagGLOfNeZero_val]
    refine cancel _ _ ?_
    rw [← hχ 1 (fun _ => one_ne_zero), e, hΦ.one, one_mulVec, one_smul]
  have hmul : ∀ s t : Fin n → ℂ, (∀ i, s i ≠ 0) → (∀ i, t i ≠ 0) → χ (s * t) = χ s * χ t := by
    intro s t hs ht
    refine cancel _ _ ?_
    rw [← hχ (s * t) (fun i => mul_ne_zero (hs i) (ht i)), diagGLOfNeZero_mul s t hs ht, hΦ.mul,
      ← mulVec_mulVec, hχ t ht, mulVec_smul, hχ s hs, smul_smul, mul_comm]
  choose Q hQ using hΦ.poly
  have hline : ∀ i : Fin n, ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ (Pi.mulSingle i t) = t ^ k := by
    intro i
    have nz : ∀ t : ℂ, t ≠ 0 → ∀ j, (Pi.mulSingle i t : Fin n → ℂ) j ≠ 0 := by
      intro t ht j
      by_cases hj : j = i
      · subst hj; simp [ht]
      · simp [Pi.mulSingle_eq_of_ne hj]
    let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ → ℂ :=
      Sum.elim (fun q t => diagonal (Pi.mulSingle i t : Fin n → ℂ) q.1 q.2)
        (fun q t => diagonal (Pi.mulSingle i t⁻¹ : Fin n → ℂ) q.1 q.2)
    have hg : ∀ s, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 → t ^ N * g s t = p.eval t := by
      rintro (⟨q1, q2⟩ | ⟨q1, q2⟩)
      · refine ⟨0, if q1 = q2 then (if q1 = i then Polynomial.X else 1) else 0, fun t ht => ?_⟩
        simp only [g, Sum.elim_inl, diagonal_apply, Pi.mulSingle_apply]
        split_ifs <;> simp
      · refine ⟨1, if q1 = q2 then (if q1 = i then 1 else Polynomial.X) else 0, fun t ht => ?_⟩
        simp only [g, Sum.elim_inr, diagonal_apply, Pi.mulSingle_apply]
        split_ifs <;> simp [ht]
    have hent : ∀ (t : ℂ) (ht : t ≠ 0) (b c : ι),
        Φ (diagGLOfNeZero (Pi.mulSingle i t) (nz t ht)) b c = MvPolynomial.eval (fun s => g s t) (Q b c) := by
      intro t ht b c
      rw [hQ]
      refine congrArg (fun x => MvPolynomial.eval x (Q b c)) ?_
      funext s
      rcases s with ⟨q1, q2⟩ | ⟨q1, q2⟩
      · simp [g, diagGLOfNeZero_val]
      · have hinv : (Pi.mulSingle i t : Fin n → ℂ)⁻¹ = Pi.mulSingle i t⁻¹ := by
          funext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Pi.mulSingle_eq_of_ne hj]
        simp only [g, Sum.elim_inr, diagGLOfNeZero_inv_val, hinv]
    let g2 : ι → ℂ → ℂ := fun c t => MvPolynomial.eval (fun s => g s t) (Q a c)
    obtain ⟨N, p, hp⟩ := GlobalTheory.T.exists_pow_mul_mvEval_eq_eval_of_laurent ι g2 (fun c => GlobalTheory.T.exists_pow_mul_mvEval_eq_eval_of_laurent _ g hg (Q a c))
      (∑ c, MvPolynomial.C (v c) * MvPolynomial.X c)
    refine GlobalTheory.T.exists_zpow_of_multiplicative_of_pow_mul_eq_eval (fun t => χ (Pi.mulSingle i t)) ?_ ?_ N (Polynomial.C (v a)⁻¹ * p) ?_
    · intro s t hs ht
      show χ (Pi.mulSingle i (s * t)) = χ (Pi.mulSingle i s) * χ (Pi.mulSingle i t)
      rw [Pi.mulSingle_mul]
      exact hmul _ _ (nz s hs) (nz t ht)
    · simpa using h1
    · intro t ht
      have e1 := congrFun (hχ _ (nz t ht)) a
      simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, hent t ht] at e1
      have e2 := hp t ht
      simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, g2] at e2
      have e3 : (∑ c, v c * MvPolynomial.eval (fun s => g s t) (Q a c)) =
          χ (Pi.mulSingle i t) * v a := by
        rw [← e1]; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
      rw [e3] at e2
      simp only [Polynomial.eval_mul, Polynomial.eval_C, ← e2]
      field_simp
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.exists_monomial_of_multiplicative_of_single_eq_zpow n χ h1 hmul hline
  refine ⟨μ, v, hv0, fun D hD => ?_⟩
  have hd : ∀ i, D.val i i ≠ 0 := by
    intro i h0
    have hdet : D.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit).ne_zero
    rw [← hD.diagonal_diag, det_diagonal] at hdet
    exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have eD : D = diagGLOfNeZero (fun i => D.val i i) hd := by
    ext1
    rw [diagGLOfNeZero_val]
    exact hD.diagonal_diag.symm
  conv_lhs => rw [eD]
  rw [hχ _ hd, hμ _ hd]

end GlobalTheory.AlgWtHW
