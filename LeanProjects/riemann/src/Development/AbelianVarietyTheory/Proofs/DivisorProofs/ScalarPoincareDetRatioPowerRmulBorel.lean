import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

noncomputable section

theorem det_ratio_pow_mul_borel_eq_weight_prod {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (k : ℕ) (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (M : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
    ((M * KU.tl X (mat b τ)).det / (M * KU.tl X (mat b τ)).toBlocks₂₂.det ^ 2) ^ k =
      (∏ i, b τ i i ^ laS X k τ i) * (M.det / M.toBlocks₂₂.det ^ 2) ^ k := by
  set T := KU.tl X (mat b τ) with hT
  have h22 : (M * T).toBlocks₂₂ = M.toBlocks₂₂ * T.toBlocks₂₂ := by
    rw [KU.toBlocks₂₂_mul, KU.tl_bor₁₂ X hb τ, Matrix.mul_zero, zero_add]
  set D1 : ℂ := ∏ j : Fin (r - X.p0), b τ (KU.eT X (Sum.inl j)) (KU.eT X (Sum.inl j)) with hD1
  set D2 : ℂ := ∏ i : Fin X.p0, b τ (KU.eT X (Sum.inr i)) (KU.eT X (Sum.inr i)) with hD2
  have hD2ne : D2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => FrameDegreeData.bdiag_ne X hb τ _
  have hdetT : T.det = D1 * D2 := by
    have ht : (mat b τ).BlockTriangular id := fun i j hij => (hb τ).2 i j hij
    rw [hT, KU.tl, Matrix.det_submatrix_equiv_self, Matrix.det_of_upperTriangular ht,
      ← Fintype.prod_equiv (KU.eT X) (fun s => mat b τ (KU.eT X s) (KU.eT X s)) _ (fun _ => rfl),
      Fintype.prod_sum_type]
    rfl
  have hdetT22 : T.toBlocks₂₂.det = D2 := by
    have ht : T.toBlocks₂₂.BlockTriangular id := by
      intro i j hij
      simp only [hT, KU.tl, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, KU.eT_inr]
      exact (hb τ).2 _ _ (show (Fin.castLE X.p0_le j : ℕ) < Fin.castLE X.p0_le i from hij)
    rw [Matrix.det_of_upperTriangular ht]
    rfl
  have hchar : (∏ i, b τ i i ^ laS X k τ i) = D1 ^ k * (D2 ^ k)⁻¹ := by
    rw [← Fintype.prod_equiv (KU.eT X) (fun s => b τ (KU.eT X s) (KU.eT X s) ^ laS X k τ (KU.eT X s)) _
      (fun _ => rfl), Fintype.prod_sum_type, hD1, hD2, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_inv_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      have : X.p0 ≤ (KU.eT X (Sum.inl j) : ℕ) := by simp [KU.eT]
      simp [laS, this]
    · refine Finset.prod_congr rfl fun i _ => ?_
      have : ¬ X.p0 ≤ (KU.eT X (Sum.inr i) : ℕ) := by simp [KU.eT]
      simp [laS, this, zpow_neg]
  rw [Matrix.det_mul, h22, Matrix.det_mul, hdetT, hdetT22, hchar, ← inv_pow, ← mul_pow, ← mul_pow]
  congr 1
  have hc : D2 * (D2 ^ 2)⁻¹ = D2⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hD2ne, one_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_inv]
  calc M.det * (D1 * D2) * ((M.toBlocks₂₂.det ^ 2)⁻¹ * (D2 ^ 2)⁻¹)
      = D1 * (D2 * (D2 ^ 2)⁻¹) * (M.det * (M.toBlocks₂₂.det ^ 2)⁻¹) := by ring
    _ = _ := by rw [hc]

theorem qS_rmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → qS X x0 k (rmul x b) = bchar (laS X k) b * qS X x0 k x := by
  intro E _ _ _ r X x0 k x b hb
  unfold qS bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [KU.Mx_rmul]
  exact det_ratio_pow_mul_borel_eq_weight_prod X k b hb τ _

end

end GlobalTheory.ScalarPoin
