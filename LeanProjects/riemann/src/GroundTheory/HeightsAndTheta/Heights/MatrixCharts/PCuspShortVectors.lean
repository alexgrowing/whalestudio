import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace CuspShortVectors

theorem intVec_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a n : Fin g → ℤ) :
    intVecC a + τ *ᵥ intVecC n =
      (fun k => ((a k : ℝ) : ℂ)) + τ *ᵥ fun k => ((n k : ℝ) : ℂ) := by
  unfold intVecC
  simp

theorem one_le_sq_of_ne_zero {m : ℤ} (hm : m ≠ 0) : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
  have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
  have h2 : (1 : ℤ) ≤ m ^ 2 := by nlinarith [sq_abs m]
  exact_mod_cast h2

theorem value_ge {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hY : (τ.map Complex.im).PosDef)
    {c M : ℝ} (hM : 0 < M)
    (hcY : ∀ x : Fin g → ℝ, c * ∑ k, x k ^ 2 ≤ MCSchur.qf (τ.map Complex.im) x)
    (hPH : PeriodHermValue.Statement) (r : ℕ)
    (hdiag : ∀ k : Fin g, r ≤ k.val → (τ.map Complex.im) k k ≤ M) (a n : Fin g → ℤ)
    (h : n ≠ 0 ∨ ∃ k : Fin g, r ≤ k.val ∧ a k ≠ 0) :
    min c (1 / M) ≤ hermValue (τ.map Complex.im)⁻¹ (intVecC a + τ *ᵥ intVecC n) := by
  have hu : IsUnit (τ.map Complex.im).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit
  rw [intVec_eq, hPH g τ hu]
  have h1 := MCCusp.qf_nonneg hY.inv.posSemidef
    ((fun k => (a k : ℝ)) + τ.map Complex.re *ᵥ fun k => (n k : ℝ))
  have h2 := MCCusp.qf_nonneg hY.posSemidef fun k => (n k : ℝ)
  by_cases hn : n = 0
  · rcases h with h | ⟨k, hk, hak⟩
    · exact absurd hn h
    have hβ : (fun k => (n k : ℝ)) = 0 := by funext k; simp [hn]
    rw [hβ, mulVec_zero, add_zero]
    have hq0 : MCSchur.qf (τ.map Complex.im) 0 = 0 := by simp [MCSchur.qf]
    rw [hq0, add_zero]
    have hsq := MCCusp.sq_le_inv_diag_mul_qf hY.inv (fun k => (a k : ℝ)) k
    rw [Matrix.nonsing_inv_nonsing_inv _ hu] at hsq
    have ha := one_le_sq_of_ne_zero hak
    have hpos : 0 < (τ.map Complex.im) k k := hY.diag_pos
    have hle := hdiag k hk
    have hq := MCCusp.qf_nonneg hY.inv.posSemidef fun k => (a k : ℝ)
    have hM' : 1 / M ≤ MCSchur.qf (τ.map Complex.im)⁻¹ fun k => (a k : ℝ) := by
      rw [div_le_iff₀ hM]
      nlinarith
    exact (min_le_right _ _).trans hM'
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp hn
    have hb := one_le_sq_of_ne_zero hk
    have hs := hcY fun k => (n k : ℝ)
    have hsum : ((n k : ℤ) : ℝ) ^ 2 ≤ ∑ j, ((n j : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun j => ((n j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)
    have hc : c ≤ MCSchur.qf (τ.map Complex.im) fun k => (n k : ℝ) := by
      rcases le_or_gt c 0 with hc0 | hc0
      · linarith
      · nlinarith
    linarith [min_le_left c (1 / M)]

end CuspShortVectors

theorem CuspShortVectors.proof (hImPos : ChartPeriodImPos.Statement)
    (hLow : ChartLowerBlockBound.Statement) (hPH : PeriodHermValue.Statement) :
    CuspShortVectors.Statement := by
  intro D T
  obtain ⟨M, hM, hMb⟩ := hLow D T
  refine ⟨Real.sqrt (min D.c (1 / M)), Real.sqrt_pos.mpr (lt_min D.c_pos (by positivity)), ?_⟩
  intro p hp hpU ℓ hℓ a n h
  obtain ⟨hY, hcY⟩ := hImPos D p.1 hpU ℓ hℓ
  unfold metricLength
  apply Real.sqrt_le_sqrt
  refine CuspShortVectors.value_ge _ hY hM hcY hPH T.r ?_ a n h
  intro k hk
  exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (hMb p hp ℓ k k hk))

end

end GroundTheory.Heights₂.Heights
