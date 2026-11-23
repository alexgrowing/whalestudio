import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Filter Topology GlobalTheory.HermFrame

namespace GlobalTheory.ChTwoBlockDiag

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [DecidableEq ι] {μ : ι → ℕ}

theorem mdel_blockDiagonal' (A : ∀ τ, E → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ) (z ξ : E) :
    mdel (fun x => blockDiagonal' fun τ => A τ x) z ξ =
      blockDiagonal' fun τ => mdel (A τ) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h
    simp only [mdel_apply, blockDiagonal'_apply_eq]
  · simp [mdel_apply, blockDiagonal'_apply_ne _ _ _ h]

theorem mdbar_blockDiagonal' (A : ∀ τ, E → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ) (z ξ : E) :
    mdbar (fun x => blockDiagonal' fun τ => A τ x) z ξ =
      blockDiagonal' fun τ => mdbar (A τ) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h
    simp only [mdbar_apply, blockDiagonal'_apply_eq]
  · simp [mdbar_apply, blockDiagonal'_apply_ne _ _ _ h]

variable [Fintype ι]

theorem inv_blockDiagonal'_of_isUnit (M : ∀ τ, Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ)
    (hu : ∀ τ, IsUnit (M τ).det) :
    (blockDiagonal' M)⁻¹ = blockDiagonal' fun τ => (M τ)⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext τ
  exact mul_nonsing_inv _ (hu τ)

theorem conn_blockDiagonal' (H : ∀ τ, E → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ) {z : E}
    (hu : ∀ τ, IsUnit (H τ z).det) (ξ : E) :
    conn (fun x => blockDiagonal' fun τ => H τ x) z ξ =
      blockDiagonal' fun τ => conn (H τ) z ξ := by
  simp only [conn]
  rw [mdel_blockDiagonal', blockDiagonal'_transpose, blockDiagonal'_transpose,
    inv_blockDiagonal'_of_isUnit _ fun τ => by rw [det_transpose]; exact hu τ,
    ← blockDiagonal'_mul]

theorem curv_blockDiagonal' {H : ∀ τ, E → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ} {z : E}
    (h : ∀ τ, MContDiffAt 2 (H τ) z) (hu : ∀ τ, IsUnit (H τ z).det) (ξ η : E) :
    curv (fun x => blockDiagonal' fun τ => H τ x) z ξ η =
      blockDiagonal' fun τ => curv (H τ) z ξ η := by
  have he : (fun x => conn (fun x => blockDiagonal' fun τ => H τ x) x ξ) =ᶠ[𝓝 z]
      fun x => blockDiagonal' fun τ => conn (H τ) x ξ := by
    filter_upwards [eventually_all.2 fun τ => (h τ).eventually_isUnit (hu τ)] with x hx
    exact conn_blockDiagonal' H hx ξ
  rw [curv, mdbar_congr he, mdbar_blockDiagonal' (fun τ x => conn (H τ) x ξ),
    ← blockDiagonal'_neg]
  rfl

theorem chTwo_blockDiagonal' {H : ∀ τ, E → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ} {z : E}
    (h : ∀ τ, MContDiffAt 2 (H τ) z) (hu : ∀ τ, IsUnit (H τ z).det) (ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo (fun x => Matrix.blockDiagonal' fun τ => H τ x) z ξ₁ η₁ ξ₂ η₂ =
      ∑ τ, chTwo (H τ) z ξ₁ η₁ ξ₂ η₂ := by
  simp only [chTwo, curv_blockDiagonal' h hu]
  rw [← Finset.mul_sum, Fintype.sum_sigma]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [blockDiagonal'_apply_eq]
  · intro j _ hj
    simp [wedge, blockDiagonal'_apply_ne _ _ _ hj]
  · simp

end GlobalTheory.ChTwoBlockDiag
