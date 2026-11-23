import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory

theorem horizForm_formAbsLe : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ (lam : Fin n → ℝ) (G : (ι → ℂ) → Matrix ι ι ℂ) (C : ℝ), TwoFormBound U H G (curv H) C →
      FormAbsLe (horizForm H π e lam y) (1 / (2 * Real.pi) * (∑ i, |lam i|) * C) (pullForm G π y) := by
  intro E _ _ _ _ _ ι _ n U H Y π A e _ hA he y hy lam G C hB
  have hU : π y ∈ U := hA.mapsTo hy
  obtain ⟨-, hG, -⟩ := hB (π y) hU
  rw [formAbsLe_iff]
  intro ξ
  set v := fderiv ℂ π y ξ with hv
  have hpull : diagVal (pullForm G π y) ξ = gnorm (G (π y)) v ^ 2 :=
    diagVal_formOf_eq_gnorm_sq hG v
  have hci : ∀ i, ‖curvDiag H π e i y ξ ξ‖ ≤ C * gnorm (G (π y)) v ^ 2 := fun i => by
    have h1 := hB.norm_form_le hU v (fun a => e y a i)
    have h2 : gnorm (H (π y)) (fun a => e y a i) ^ 2 = 1 := by
      rw [gnorm_sq (hB (π y) hU).1.posSemidef, he.unitary y hy i i, if_pos rfl, one_re]
    rw [h2, mul_one] at h1
    exact h1
  set S : ℂ := ∑ i, (lam i : ℂ) * curvDiag H π e i y ξ ξ with hS
  have hdiag : diagVal (horizForm H π e lam y) ξ = -(1 / (2 * Real.pi)) * S.re := by
    have h2π : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
    have : -I * horizForm H π e lam y ξ ξ = ((-(1 / (2 * Real.pi)) : ℝ) : ℂ) * S := by
      rw [horizForm, kappa, ← hS]
      push_cast at h2π ⊢
      field_simp
      linear_combination S * I_sq
    rw [diagVal, this, re_ofReal_mul]
  have hSre : S.re = ∑ i, lam i * (curvDiag H π e i y ξ ξ).re := by
    rw [hS, re_sum]; exact Finset.sum_congr rfl fun i _ => re_ofReal_mul _ _
  rw [hdiag, hSre, hpull, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
  have hsum : |∑ i, lam i * (curvDiag H π e i y ξ ξ).re| ≤
      ∑ i, |lam i| * (C * gnorm (G (π y)) v ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_re_le_norm _).trans (hci i)) (abs_nonneg _)
  calc 1 / (2 * Real.pi) * |∑ i, lam i * (curvDiag H π e i y ξ ξ).re|
      ≤ 1 / (2 * Real.pi) * ∑ i, |lam i| * (C * gnorm (G (π y)) v ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 / (2 * Real.pi) * (∑ i, |lam i|) * C * gnorm (G (π y)) v ^ 2 := by
        rw [← Finset.sum_mul]; ring

end GlobalTheory
