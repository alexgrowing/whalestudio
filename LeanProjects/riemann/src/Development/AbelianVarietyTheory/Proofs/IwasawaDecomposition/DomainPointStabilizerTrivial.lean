import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDetNeZeroFirstCol

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FreeOnDomain

theorem exists_conj_first_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ P B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, P.det ≠ 0 ∧ (∀ a : Fin n, B a.succ 0 = 0) ∧ A * P = P * B := by
  first
  | exact @_root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero
  | exact _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero
  | (apply _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero ..)

theorem exists_conj_triangular (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ P T : Matrix (Fin n) (Fin n) ℂ, P.det ≠ 0 ∧ (∀ a c, c < a → T a c = 0) ∧ A * P = P * T := by
  induction n with
  | zero => exact ⟨1, 1, by simp, fun a => a.elim0, Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨P, B, hP, hB, e⟩ := exists_conj_first_col A
    obtain ⟨Q, T, hQ, hT, e'⟩ := ih (B.submatrix Fin.succ Fin.succ)
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      of (Fin.cons (Fin.cons 1 fun _ => 0) fun a => Fin.cons 0 (Q a))
    let T' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      of (Fin.cons ((B * D) 0) fun a => Fin.cons 0 (T a))
    have hD : D.det = Q.det := by
      rw [det_succ_row_zero, Fin.sum_univ_succ]
      simp only [D, of_apply, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      rfl
    have hBD : B * D = D * T' := by
      ext a c
      refine Fin.cases ?_ (fun a => ?_) a
      · rw [mul_apply (M := D), Fin.sum_univ_succ]
        simp [D, T']
      · refine Fin.cases ?_ (fun c => ?_) c
        · simp [D, T', mul_apply, Fin.sum_univ_succ, hB]
        · have := congrFun (congrFun e' a) c
          simpa [D, T', mul_apply, Fin.sum_univ_succ] using this
    refine ⟨P * D, T', ?_, fun a c h => ?_, ?_⟩
    · rw [det_mul, hD]; exact mul_ne_zero hP hQ
    · revert h
      refine Fin.cases ?_ (fun a => ?_) a
      · intro h; exact absurd h (by simp)
      · refine Fin.cases ?_ (fun c => ?_) c
        · intro _; simp [T']
        · intro h; simpa [T'] using hT a c (Fin.succ_lt_succ_iff.1 h)
    · rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, hBD, Matrix.mul_assoc]

theorem toBlocks₁₂_eq_zero {p q : ℕ} {F F' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hF : IsUnit F.det)
    (h2 : IsUnit F.toBlocks₂₂.det) (h2' : IsUnit F'.toBlocks₂₂.det) (h : moeb F' 0 = moeb F 0) :
    (F⁻¹ * F').toBlocks₁₂ = 0 := by
  rw [moeb_zero, moeb_zero] at h
  have h1 : F'.toBlocks₁₂ = F.toBlocks₁₂ * (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    rw [← Matrix.mul_assoc, ← h, nonsing_inv_mul_cancel_right _ _ h2']
  have e : F' * fromBlocks 0 0 0 1 =
      F * fromBlocks (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    conv_lhs => rw [← fromBlocks_toBlocks F']
    conv_rhs => enter [1]; rw [← fromBlocks_toBlocks F]
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, ← h1, mul_nonsing_inv_cancel_left _ _ h2]
  have e2 : (F⁻¹ * F') * fromBlocks 0 0 0 1 =
      fromBlocks (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    rw [Matrix.mul_assoc, e, nonsing_inv_mul_cancel_left _ _ hF]
  rw [← fromBlocks_toBlocks (F⁻¹ * F'), fromBlocks_multiply] at e2
  simpa using congrArg toBlocks₁₂ e2

theorem exists_conj_block {r j : ℕ} (hj : j ≤ r) (M : Matrix (Fin r) (Fin r) ℂ)
    (hM : (reindex (idx hj) (idx hj) M).toBlocks₁₂ = 0) :
    ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧ (∀ a c : Fin r, (c : ℕ) < r - j → ¬ (a : ℕ) < r - j → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ M * b = b * t := by
  set G := reindex (idx hj) (idx hj) M with hG
  obtain ⟨P, T, hP, hT, e⟩ := exists_conj_triangular _ G.toBlocks₁₁
  obtain ⟨Q, S, hQ, hS, e'⟩ := exists_conj_triangular _ G.toBlocks₂₂
  have hm : G * fromBlocks P 0 0 Q = fromBlocks P 0 0 Q * fromBlocks T 0 (Q⁻¹ * (G.toBlocks₂₁ * P)) S := by
    conv_lhs => rw [← fromBlocks_toBlocks G, hM]
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e, e', mul_nonsing_inv_cancel_left _ _ hQ.isUnit]
  refine ⟨(fromBlocks P 0 0 Q).submatrix (idx hj) (idx hj),
    (fromBlocks T 0 (Q⁻¹ * (G.toBlocks₂₁ * P)) S).submatrix (idx hj) (idx hj), ?_, fun a c hc ha => ?_,
    fun a c h => ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; exact mul_ne_zero hP hQ
  · obtain ⟨a, rfl⟩ := (idx hj).symm.surjective a
    obtain ⟨c, rfl⟩ := (idx hj).symm.surjective c
    rcases a with a | a <;> rcases c with c | c
    · rw [idx_symm_inl] at hc; omega
    · simp
    · simp
    · rw [idx_symm_inr] at ha; exact absurd a.2 ha
  · obtain ⟨a, rfl⟩ := (idx hj).symm.surjective a
    obtain ⟨c, rfl⟩ := (idx hj).symm.surjective c
    rw [Fin.lt_def] at h
    rcases a with a | a <;> rcases c with c | c
    · rw [idx_symm_inl, idx_symm_inl] at h
      simpa using hT a c (by rw [Fin.lt_def]; omega)
    · simp
    · rw [idx_symm_inl, idx_symm_inr] at h
      have := a.2; omega
    · rw [idx_symm_inr, idx_symm_inr] at h
      simpa using hS a c h
  · have : M = G.submatrix (idx hj) (idx hj) := by simp [hG]
    rw [submatrix_mul_equiv, ← hm, ← submatrix_mul_equiv _ _ _ (idx hj), ← this]

theorem eq_one_of_domPt_lact_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1 := by
  intro E _ _ _ r j X hj Tau _ κ hp γ hγ x hx h
  obtain ⟨x, ho, b₀, hb₀, rfl⟩ := ortho_holds r X x hx
  rw [KU.lact_rmul', domPt_rmul X hj κ hb₀, domPt_rmul X hj κ hb₀] at h
  have hx := IC.orth_mem_dom X ho
  have hx' := IC.orth_mem_dom X (KU.isOrth_lact X hγ ho)
  have key : ∀ τ : X.Ψ, ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧
      (∀ a c : Fin r, (c : ℕ) < r - j → ¬ (a : ℕ) < r - j → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ (mat x τ)⁻¹ * mat (lact γ x) τ * b = b * t := by
    intro τ
    refine exists_conj_block hj _ ?_
    obtain ⟨s, rfl⟩ := κ.surjective τ
    have u0 : IsUnit (mat (x0F X) (κ s)).det := (det_x0F X _).isUnit
    have hF : IsUnit (frameCo X hj x (κ s)).det := by
      rw [frameCo, det_reindex_self, det_mul]
      exact (isUnit_nonsing_inv_det _ u0).mul (hx _).1.isUnit
    have := toBlocks₁₂_eq_zero hF (frameCo_isUnit₂₂ X hj hp hx _) (frameCo_isUnit₂₂ X hj hp hx' _) (congrFun h s)
    rw [frameCo, frameCo, inv_reindex, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ u0] at this
    simp only [reindex_apply, submatrix_mul_equiv] at this ⊢
    rwa [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ u0] at this
  choose b t hb hb0 ht e using key
  have e' : ∀ τ, mat (lact γ x) τ * b τ = mat x τ * b τ * t τ := fun τ => by
    rw [Matrix.mul_assoc, ← e, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (hx τ).1.isUnit]
  refine X.Γ_free γ hγ (rmul x fun τ => b τ)
    (GlobalTheory.PointOfFrames.rmul_mem_dom X hx _ hb (by rw [hp]; exact hb0)) (fun τ => t τ) (fun τ => ⟨?_, ht τ⟩) ?_
  · intro h0
    have h1 := congrArg det (e' τ)
    have h0' : (t τ).det = 0 := h0
    rw [det_mul, det_mul, h0', mul_zero] at h1
    exact mul_ne_zero (hx' τ).1 (hb τ) h1
  · exact (KU.lact_rmul' X γ x _).trans (funext e')

end GlobalTheory.FreeOnDomain
