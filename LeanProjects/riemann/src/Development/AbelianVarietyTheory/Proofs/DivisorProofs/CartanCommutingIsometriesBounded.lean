import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.CartanBound

open Matrix

def cq {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ℝ := ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x).re

lemma cq_continuous {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) : Continuous (cq M θ) := by
  unfold cq
  exact Complex.continuous_re.comp ((continuous_const.matrix_mulVec continuous_id).dotProduct
    (continuous_const.matrix_mulVec continuous_star))

lemma cq_smul {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (x : Fin n → ℂ) :
    cq M θ ((r : ℂ) • x) = r ^ 2 * cq M θ x := by
  unfold cq
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, Matrix.mulVec_smul, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  ring

lemma cq_zero {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) : cq M θ 0 = 0 := by simp [cq]

lemma star_mulVec_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star (A *ᵥ x) = A.map star *ᵥ star x := by
  funext i
  simp [Matrix.mulVec, dotProduct, star_sum]

lemma cq_iso {n : ℕ} (M θ A : Matrix (Fin n) (Fin n) ℂ) (hA : A.transpose * M * A.map star = M)
    (hθ : A * θ = θ * A) (x : Fin n → ℂ) : cq M θ (A *ᵥ x) = cq M θ x := by
  unfold cq
  congr 1
  have h1 : θ *ᵥ (A *ᵥ x) = A *ᵥ (θ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, ← hθ, ← Matrix.mulVec_mulVec]
  have h2 : ∀ y w : Fin n → ℂ, (A *ᵥ y) ⬝ᵥ M *ᵥ (A.map star *ᵥ w) = y ⬝ᵥ M *ᵥ w := by
    intro y w
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
  rw [h1, star_mulVec_eq, h2]

end GlobalTheory.CartanBound

namespace GlobalTheory

open Matrix GlobalTheory.CartanBound in

theorem isCartan_entries_bounded : ∀ {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ →
    ∃ R : ℝ, ∀ A : Matrix (Fin n) (Fin n) ℂ, A.transpose * M * A.map star = M → A * θ = θ * A →
      ∀ i j, ‖A i j‖ ≤ R := by
  intro n M θ hC
  cases n with
  | zero => exact ⟨0, fun _ _ _ i => i.elim0⟩
  | succ m =>
    obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : Fin (m + 1) → ℂ) 1).exists_isMinOn
      ⟨Pi.single 0 1, by simp [Pi.norm_single]⟩ (cq_continuous M θ).continuousOn
    have hu0' : ‖u0‖ = 1 := by simpa using hu0
    have hc : 0 < cq M θ u0 := hC.2.2 u0 (by rintro rfl; simp at hu0')
    have key : ∀ y, cq M θ u0 * ‖y‖ ^ 2 ≤ cq M θ y := by
      intro y
      by_cases hy : y = 0
      · simp [hy, cq_zero]
      have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
      have hu : ((‖y‖⁻¹ : ℝ) : ℂ) • y ∈ Metric.sphere (0 : Fin (m + 1) → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
      have hyu : y = ((‖y‖ : ℝ) : ℂ) • (((‖y‖⁻¹ : ℝ) : ℂ) • y) := by
        rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
      have h2 : cq M θ y = ‖y‖ ^ 2 * cq M θ (((‖y‖⁻¹ : ℝ) : ℂ) • y) := by
        conv_lhs => rw [hyu]
        exact cq_smul M θ _ _
      rw [h2, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin hu) (sq_nonneg _)
    refine ⟨Real.sqrt ((∑ k, |cq M θ (Pi.single k 1)|) / cq M θ u0), fun A hA hθA i j => ?_⟩
    have h1 : ‖A i j‖ ≤ ‖A *ᵥ Pi.single j 1‖ := by
      have := norm_le_pi_norm (A *ᵥ Pi.single j 1) i
      simpa using this
    have h2 : cq M θ u0 * ‖A *ᵥ Pi.single j 1‖ ^ 2 ≤ ∑ k, |cq M θ (Pi.single k 1)| := by
      refine (key _).trans ?_
      rw [cq_iso M θ A hA hθA]
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun k => |cq M θ (Pi.single k 1)|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ j))
    refine h1.trans (Real.le_sqrt_of_sq_le ?_)
    rw [le_div_iff₀ hc, mul_comm]
    exact h2

end GlobalTheory

end
