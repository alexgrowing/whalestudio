import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunction
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.RealMove

open GlobalTheory.Unf GlobalTheory.Unf.MajMeas

theorem realSize_mul_le_mul {D : D7} (θ : InfFam D) {m r n : ℕ} (Y : Mx D m r) (a : Mx D r n) :
    realSize θ (Y * a) ≤ n * realSize θ Y * realSize θ a := by
  calc realSize θ (Y * a) = ∑ τ, ∑ i, ∑ j, ‖∑ l, compAt θ τ Y i l * compAt θ τ a l j‖ := by
        simp only [realSize, compAt_mul, Matrix.mul_apply]
    _ ≤ ∑ τ, ∑ i, ∑ _j : Fin n, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a := by
        gcongr with τ _ i _ j _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_compAt_le_realSize θ a τ l j) (norm_nonneg _)
    _ = n * realSize θ Y * realSize θ a := by
        have h : ∀ τ i, ∑ _j : Fin n, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a =
            n * (∑ l, ‖compAt θ τ Y i l‖) * realSize θ a := by
          intro τ i
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, mul_assoc]
        simp_rw [h, ← Finset.sum_mul, ← Finset.mul_sum]
        rfl

theorem realSize_le_of_isCompact : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.realSize θ x ≤ C * GlobalTheory.Unf.realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := by
  intro D θ hθ V n Q hQ
  have hc : Continuous (fun y : GA D V => realSize θ (Formalism.L2.Theta.mt V y)) :=
    (continuous_realSize hθ).comp (GlobalTheory.Core.Rk.Level.continuous_mt' V)
  obtain ⟨M, hM⟩ := (hQ.image hc).bddAbove
  refine ⟨max 1 (n * M), le_max_left _ _, fun y hy x => ?_⟩
  set a : Mx D V.rank n := HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x with ha
  have e : x = (HMul.hMul (Formalism.L2.Theta.mt V y) a : Mx D V.rank n) := by
    rw [ha]
    rw [← Matrix.mul_assoc, ← GlobalTheory.Core.Rk.Level.mt_mul', mul_inv_cancel, GlobalTheory.Core.Rk.Level.mt_one',
      Matrix.one_mul]
  have hyM : realSize θ (Formalism.L2.Theta.mt V y) ≤ M := hM ⟨y, hy, rfl⟩
  have h0 := realSize_nonneg θ a
  have h1 := realSize_nonneg θ (Formalism.L2.Theta.mt V y)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc realSize θ x = realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y) a : Mx D V.rank n) := by rw [← e]
    _ ≤ n * realSize θ (Formalism.L2.Theta.mt V y) * realSize θ a :=
        realSize_mul_le_mul θ _ _
    _ ≤ (n * M) * realSize θ a := by gcongr
    _ ≤ max 1 (n * M) * realSize θ a := by gcongr; exact le_max_right _ _

end GlobalTheory.Unf.RealMove
