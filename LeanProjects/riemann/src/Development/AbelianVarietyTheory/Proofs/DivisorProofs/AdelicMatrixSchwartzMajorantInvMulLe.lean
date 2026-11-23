import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactBoxOfUnitaryTranslateCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixRealSizeLeConstMulOfCompactTranslateStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MajMul

theorem maj_mul_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) ≤ C * GlobalTheory.Unf.maj θ K' N x := by
  intro D θ hθ V n Q hQ K hK
  obtain ⟨K', hK', hbox⟩ := GlobalTheory.T.exists_compactBox_of_unitaryTranslate_compact D V n Q hQ K hK
  obtain ⟨C₀, hC₀, hreal⟩ := GlobalTheory.T.adelicMatrixRealSize_le_const_mul_of_compact_translate D θ hθ V n Q hQ
  refine ⟨K', hK', fun N => ⟨C₀ ^ N, by positivity, fun y hy x => ?_⟩⟩
  set z : Mx D V.rank n := HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x with hz
  unfold GlobalTheory.Unf.maj
  by_cases hin : GlobalTheory.Unf.InBox K z
  · rw [if_pos hin, if_pos (hbox y hy x hin)]
    have h0 := GlobalTheory.Unf.realSize_nonneg θ z
    have h1 := GlobalTheory.Unf.realSize_nonneg θ x
    have h2 := hreal y hy x
    have h3 : 1 + GlobalTheory.Unf.realSize θ x ≤ C₀ * (1 + GlobalTheory.Unf.realSize θ z) := by nlinarith
    have hp : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ x) ^ N := by positivity
    have hq : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ z) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ (C₀ * (1 + GlobalTheory.Unf.realSize θ z)) ^ N := by gcongr
      _ = C₀ ^ N * (1 + GlobalTheory.Unf.realSize θ z) ^ N := by rw [mul_pow]
  · rw [if_neg hin]
    have := GlobalTheory.Unf.maj_nonneg θ K' N x
    unfold GlobalTheory.Unf.maj at this
    have hC : (0:ℝ) ≤ C₀ ^ N := by positivity
    exact mul_nonneg hC this

end GlobalTheory.MajMul
