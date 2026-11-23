import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

theorem conj_mem_realLie : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (Y : X.Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ a b, Y τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (Y τ a b) = 0) → (∀ τ a, Y τ a a = 0) → (fun τ => ((mat x τ * Y τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ)) ∈ realLie X.Ψ X.Gm := by
  intro E _ _ _ r X x hx Y hY hd
  intro τ
  set A : Matrix (Fin r) (Fin r) ℂ := mat x τ with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  set D : Matrix (Fin r) (Fin r) ℂ := A * Y τ * A⁻¹ with hDdef
  have hDA : D * A = A * Y τ := by
    rw [hDdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · change (A * Y τ * A⁻¹).trace = 0
    rw [Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    simp only [Matrix.trace, Matrix.diag, hd, Finset.sum_const_zero]
  · intro u w
    change hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) = 0
    clear_value D
    set Gt : Matrix (Fin r) (Fin r) ℂ := X.Gm.map τ.1 with hGt
    have hform : ∀ u v : Fin r → ℂ, hermC τ.1 X.Gm u v = u ⬝ᵥ (Gt *ᵥ (fun b => conj (v b))) := by
      intro u v
      simp only [hermC, dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [hGt, Matrix.map_apply]
      ring
    have hconj : ∀ v : Fin r → ℂ, (fun b => conj ((D *ᵥ v) b)) = D.map (starRingEnd ℂ) *ᵥ (fun b => conj (v b)) := by
      intro v
      funext b
      simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    set M : Matrix (Fin r) (Fin r) ℂ := Dᵀ * Gt + Gt * D.map (starRingEnd ℂ) with hMdef
    have hsum : hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) =
        u ⬝ᵥ (M *ᵥ (fun b => conj (w b))) := by
      rw [hform, hform, hconj, hMdef, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
      congr 1
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
    have hJ : Aᵀ * Gt * A.map (starRingEnd ℂ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
      rw [hGt, ← FrameDegreeData.gram_eq]
      exact hx τ
    have hkey : Aᵀ * M * A.map (starRingEnd ℂ) = 0 := by
      have e1 : Aᵀ * M * A.map (starRingEnd ℂ) =
          (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) := by
        rw [hMdef, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      have e2 : (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) =
          (Y τ)ᵀ * (Aᵀ * Gt * A.map (starRingEnd ℂ)) + (Aᵀ * Gt * A.map (starRingEnd ℂ)) * (Y τ).map (starRingEnd ℂ) := by
        rw [hDA, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_assoc]
      rw [e1, e2, hJ]
      ext a b
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
        Matrix.map_apply, Matrix.zero_apply]
      exact hY τ a b
    have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
    have hAc : IsUnit (A.map (starRingEnd ℂ)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact hA.map _
    have hM : M = 0 := by
      calc M = Aᵀ⁻¹ * (Aᵀ * M * A.map (starRingEnd ℂ)) * (A.map (starRingEnd ℂ))⁻¹ := by
            rw [Matrix.mul_assoc Aᵀ, Matrix.nonsing_inv_mul_cancel_left _ _ hAt,
              Matrix.mul_nonsing_inv_cancel_right _ _ hAc]
        _ = 0 := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul]
    rw [hsum, hM, Matrix.zero_mulVec, dotProduct_zero]

end GlobalTheory.SUChartSection
