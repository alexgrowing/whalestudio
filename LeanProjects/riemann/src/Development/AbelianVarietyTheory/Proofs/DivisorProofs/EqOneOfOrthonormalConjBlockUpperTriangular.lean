import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivial

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin

namespace GlobalTheory.ScalarPoin.BlockFree

theorem eq_one_of_gm_toBlocks₁₂ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, (∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) → γ = 1 := by
  intro E _ _ _ r X x0 ho γ hγ h
  have hj : r - X.p0 ≤ r := Nat.sub_le _ _
  have hp : r - (r - X.p0) = X.p0 := Nat.sub_sub_self X.p0_le
  have hx := IC.orth_mem_dom X ho
  have hx' := IC.orth_mem_dom X (KU.isOrth_lact X hγ ho)
  have key : ∀ τ : X.Ψ, ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧
      (∀ a c : Fin r, (c : ℕ) < r - (r - X.p0) → ¬ (a : ℕ) < r - (r - X.p0) → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ (mat x0 τ)⁻¹ * mat (lact γ x0) τ * b = b * t := by
    intro τ
    refine GlobalTheory.FreeOnDomain.exists_conj_block hj _ ?_
    ext u v
    have e1 : (GlobalTheory.TrueCx.idx hj).symm (Sum.inl u) = KU.eT X (Sum.inl u) := by
      apply Fin.ext
      rw [GlobalTheory.TrueCx.idx_symm_inl, KU.eT_inl]
      simp only [ExF.qI]
      omega
    have e2 : (GlobalTheory.TrueCx.idx hj).symm (Sum.inr v) = KU.eT X (Sum.inr (Fin.cast hp v)) := by
      apply Fin.ext
      rw [GlobalTheory.TrueCx.idx_symm_inr, KU.eT_inr]
      simp
    have hz := congrFun (congrFun (h τ) u) (Fin.cast hp v)
    simp only [KU.gm, KU.tl, toBlocks₁₂, of_apply, submatrix_apply, Matrix.zero_apply] at hz
    simp only [toBlocks₁₂, reindex_apply, of_apply, submatrix_apply, Matrix.zero_apply, e1, e2]
    rw [← hz, Matrix.mul_assoc]
    rfl
  choose b t hb hb0 ht e using key
  have e' : ∀ τ, mat (lact γ x0) τ * b τ = mat x0 τ * b τ * t τ := fun τ => by
    rw [Matrix.mul_assoc, ← e, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (hx τ).1.isUnit]
  refine X.Γ_free γ hγ (rmul x0 fun τ => b τ)
    (GlobalTheory.PointOfFrames.rmul_mem_dom X hx _ hb (fun τ a c h1 h2 => hb0 τ a c (by rw [hp]; exact h1)
      (by rw [hp]; exact h2))) (fun τ => t τ) (fun τ => ⟨?_, ht τ⟩) ?_
  · intro h0
    have h1 := congrArg det (e' τ)
    have h0' : (t τ).det = 0 := h0
    rw [det_mul, det_mul, h0', mul_zero] at h1
    exact mul_ne_zero (hx' τ).1 (hb τ) h1
  · exact (KU.lact_rmul' X γ x0 _).trans (funext e')

end GlobalTheory.ScalarPoin.BlockFree
