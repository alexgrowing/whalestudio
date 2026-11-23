import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem GlobalTheory.upperTriangular_signForm_diagonal : ∀ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℂ) (s : Fin r → ℝ), (∀ a, s a = 1 ∨ s a = -1) → IsUnit b.det → (∀ a c : Fin r, c < a → b a c = 0) → bᵀ * diagonal (fun a => (s a : ℂ)) * b.map (starRingEnd ℂ) = diagonal (fun a => (s a : ℂ)) → (∀ a c : Fin r, a ≠ c → b a c = 0) ∧ ∀ a, ‖b a a‖ = 1 := by
  intro r b s hs hdet hup hJ
  classical
  set J : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => (s a : ℂ)) with hJdef
  have hss : ∀ a, (s a : ℂ) * (s a : ℂ) = 1 := by
    intro a; rcases hs a with h | h <;> simp [h]
  have hJJ : J * J = 1 := by
    rw [hJdef, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hss]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hbt : BlockTriangular b id := fun i j hij => hup i j hij
  haveI : Invertible b := b.invertibleOfIsUnitDet hdet
  have hinv : BlockTriangular b⁻¹ id := blockTriangular_inv_of_blockTriangular hbt
  have hright : bᵀ * (J * b.map (starRingEnd ℂ) * J) = 1 := by
    calc bᵀ * (J * b.map (starRingEnd ℂ) * J) = (bᵀ * J * b.map (starRingEnd ℂ)) * J := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have heq : J * b.map (starRingEnd ℂ) * J = (bᵀ)⁻¹ := (Matrix.inv_eq_right_inv hright).symm
  rw [← Matrix.transpose_nonsing_inv] at heq
  have hoff : ∀ a c : Fin r, a < c → b a c = 0 := by
    intro a c hac
    have h1 := congrFun (congrFun heq a) c
    have h2 : (b⁻¹)ᵀ a c = 0 := by
      rw [transpose_apply]; exact hinv hac
    rw [h2, hJdef, mul_diagonal, diagonal_mul] at h1
    simp only [map_apply] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have hsc : (s c : ℂ) ≠ 0 := by rcases hs c with h | h <;> simp [h]
    have : (starRingEnd ℂ) (b a c) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hsa
        · exact h
      · exact absurd h hsc
    simpa using this
  have hdiag : ∀ a c : Fin r, a ≠ c → b a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact hoff a c h
    · exact hup a c h
  refine ⟨hdiag, fun a => ?_⟩
  have h1 := congrFun (congrFun hJ a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · have hJaa : J a a = (s a : ℂ) := by simp [hJdef]
    rw [mul_diagonal, transpose_apply, map_apply, hJaa] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have h2 : b a a * (starRingEnd ℂ) (b a a) = 1 := by
      have : (s a : ℂ) * (b a a * (starRingEnd ℂ) (b a a)) = (s a : ℂ) * 1 := by
        linear_combination h1
      exact mul_left_cancel₀ hsa this
    rw [Complex.mul_conj] at h2
    have h3 : Complex.normSq (b a a) = 1 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq] at h3
    have h4 : 0 ≤ ‖b a a‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖b a a‖ - 1), sq_nonneg (‖b a a‖ + 1)]
  · intro k _ hk
    rw [mul_diagonal, transpose_apply, map_apply, hdiag k a hk]
    simp
  · intro h; exact absurd (Finset.mem_univ a) h
