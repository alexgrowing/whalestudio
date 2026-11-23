import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TorusFrame

theorem sum_angles {r : ℕ} (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ (Fin.castSucc i) = φ ⟨i, by simpa using i.isLt⟩ := by
      intro i; unfold angles; rw [dif_pos (by simpa using i.isLt)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dif_neg (by simp)]
    rw [h2, Finset.sum_congr rfl (fun i _ => h1 i)]
    simp

theorem hermC_eq_dot {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  simp only [hermC, dotProduct, mulVec, map_apply, Finset.mul_sum, mul_assoc]

theorem conj_mulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => (starRingEnd ℂ) ((M *ᵥ w) b)) = M.map (starRingEnd ℂ) *ᵥ fun b => (starRingEnd ℂ) (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem hermC_mulVec {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ w) = u ⬝ᵥ ((Mᵀ * G.map τ * M.map (starRingEnd ℂ)) *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  rw [hermC_eq_dot, conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_phase {r : ℕ} (φ : Fin (r - 1) → ℝ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).det = 1 := by
  rw [det_diagonal, ← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, sum_angles]
  simp

theorem phase_gram {r : ℕ} (φ : Fin (r - 1) → ℝ) (s : Fin r → ℂ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ))))ᵀ * diagonal s *
      (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).map (starRingEnd ℂ) = diagonal s := by
  rw [diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext a
  rw [← Complex.exp_conj, mul_comm (Complex.exp _) (s a), mul_assoc, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

theorem torusGL_mem_realSU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ), torusGL hx θ ∈ realSU X.Ψ X.Gm := by
  intro E _ _ _ r X x hx θ
  intro τ
  have hu := isUnit_det_of_isOrth hx τ
  rw [torusGL_val]
  refine ⟨?_, fun u w => ?_⟩
  · rw [det_mul, det_mul, det_phase, mul_one, det_nonsing_inv, Ring.mul_inverse_cancel _ hu]
  · rw [hermC_mulVec, hermC_eq_dot]
    congr 2
    have hG := hx τ
    rw [gram_eq] at hG
    have h1 : (mat x τ)⁻¹ᵀ * (mat x τ)ᵀ = 1 := by
      rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
    have h2 : (mat x τ).map (starRingEnd ℂ) * ((mat x τ)⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGτ : X.Gm.map τ.1 = (mat x τ)⁻¹ᵀ * ((mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ)) *
        ((mat x τ)⁻¹).map (starRingEnd ℂ) := by
      rw [Matrix.mul_assoc _ _ ((mat x τ)⁻¹.map _), Matrix.mul_assoc _ ((mat x τ).map _), h2, Matrix.mul_one,
        ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [hG] at hGτ
    simp only [transpose_mul, Matrix.map_mul]
    rw [hGτ]
    have h1' : (mat x τ)ᵀ * (mat x τ)⁻¹ᵀ = 1 := by
      rw [← transpose_mul, nonsing_inv_mul _ hu, transpose_one]
    have h2' : ((mat x τ)⁻¹).map (starRingEnd ℂ) * (mat x τ).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have key := fun (Q : Matrix (Fin r) (Fin r) ℂ) =>
      (show (diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ)))ᵀ *
          ((diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
          ((diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))).map (starRingEnd ℂ) * Q)) =
          (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * Q by
        simp only [← Matrix.mul_assoc, phase_gram])
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (mat x τ)ᵀ, h1', Matrix.one_mul, ← Matrix.mul_assoc ((mat x τ)⁻¹.map _), h2',
      Matrix.one_mul, key]

end GlobalTheory.TorusFrame
