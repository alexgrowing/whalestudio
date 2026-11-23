import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

open Matrix

noncomputable section

theorem normSq_det_of_isUpq {p q : ℕ} {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    Complex.normSq g.det = 1 := by
  have hJ : (Jf p q).det * (Jf p q).det = 1 := by
    rw [← det_mul, sumBdJf_mul_Jf, det_one]
  have hJ0 : (Jf p q).det ≠ 0 := left_ne_zero_of_mul_eq_one hJ
  have h1 := congrArg det (show gᴴ * Jf p q * g = Jf p q from h)
  rw [det_mul, det_mul, det_conjTranspose] at h1
  have h2 : ((Complex.normSq g.det : ℂ) - 1) * (Jf p q).det = 0 := by
    rw [Complex.normSq_eq_conj_mul_self]
    have : star g.det = (starRingEnd ℂ) g.det := rfl
    rw [this] at h1
    linear_combination h1
  have h3 := (mul_eq_zero.1 h2).resolve_right hJ0
  exact_mod_cast sub_eq_zero.1 h3

theorem norm_det_of_isUpq {p q : ℕ} {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    ‖g.det‖ = 1 := by
  have h1 := normSq_det_of_isUpq h
  rw [Complex.normSq_eq_norm_sq] at h1
  have h0 := norm_nonneg g.det
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem Mx_self (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) :
    KU.Mx X x0 x0 τ = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [KU.Mx, Matrix.nonsing_inv_mul _ hu, KU.tl, Matrix.submatrix_one_equiv]

theorem norm_fac_lact (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    ‖(KU.Mx X x0 (lact γ x0) τ).det / (KU.Mx X x0 (lact γ x0) τ).toBlocks₂₂.det ^ 2‖ =
      (Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det)⁻¹ := by
  rw [KU.Mx_lact X ho, Mx_self X ho, Matrix.mul_one, norm_div, norm_pow,
    norm_det_of_isUpq (KU.gm_upq X ho hγ τ), Complex.normSq_eq_norm_sq, one_div]

theorem one_add_fsq_le (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    1 + sumBdFsq (KU.gm X x0 γ τ).toBlocks₁₂ ≤ Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det :=
  sumBd_detD_ge (KU.gm_upq X ho hγ τ)

theorem norm_qS_lact_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, ‖qS X x0 1 (lact γ x0)‖ ≤ 1 ∧
      (‖qS X x0 1 (lact γ x0)‖ = 1 → ∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) := by
  intro E _ _ _ r X x0 ho γ hγ
  classical
  set N : X.Ψ → ℝ := fun τ => Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det with hNdef
  have hF : ∀ τ, 1 + sumBdFsq (KU.gm X x0 γ τ).toBlocks₁₂ ≤ N τ := fun τ => one_add_fsq_le X ho hγ τ
  have hN1 : ∀ τ, 1 ≤ N τ := fun τ => by
    have := sumBdFsq_nonneg (KU.gm X x0 γ τ).toBlocks₁₂; linarith [hF τ]
  have hq : ‖qS X x0 1 (lact γ x0)‖ = ∏ τ, (N τ)⁻¹ := by
    simp only [qS, pow_one]
    rw [norm_prod]
    exact Finset.prod_congr rfl fun τ _ => norm_fac_lact X ho hγ τ
  have ha0 : ∀ τ, 0 ≤ (N τ)⁻¹ := fun τ => inv_nonneg.2 (by linarith [hN1 τ])
  have ha1 : ∀ τ, (N τ)⁻¹ ≤ 1 := fun τ => inv_le_one_of_one_le₀ (hN1 τ)
  refine ⟨?_, fun h1 σ => ?_⟩
  · rw [hq]; exact Finset.prod_le_one (fun τ _ => ha0 τ) (fun τ _ => ha1 τ)
  · rw [hq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ)] at h1
    have hP0 : 0 ≤ ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ := Finset.prod_nonneg fun τ _ => ha0 τ
    have hP1 : ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ ≤ 1 := Finset.prod_le_one (fun τ _ => ha0 τ) (fun τ _ => ha1 τ)
    have hs : 1 ≤ (N σ)⁻¹ := by
      calc (1 : ℝ) = (N σ)⁻¹ * ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ := h1.symm
        _ ≤ (N σ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hP1 (ha0 σ)
        _ = (N σ)⁻¹ := mul_one _
    have hNs : N σ ≤ 1 := by
      have hpos : 0 < N σ := by linarith [hN1 σ]
      rw [le_inv_comm₀ one_pos hpos, inv_one] at hs
      exact hs
    have hF0 : sumBdFsq (KU.gm X x0 γ σ).toBlocks₁₂ ≤ 0 := by linarith [hF σ]
    ext i j
    have he := sumBd_entry_le_fsq (KU.gm X x0 γ σ).toBlocks₁₂ i j
    have : Complex.normSq ((KU.gm X x0 γ σ).toBlocks₁₂ i j) = 0 :=
      le_antisymm (by linarith) (Complex.normSq_nonneg _)
    simpa using this

end

end GlobalTheory.ScalarPoin
