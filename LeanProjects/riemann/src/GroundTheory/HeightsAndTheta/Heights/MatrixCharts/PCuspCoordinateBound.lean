import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace CuspCoordinateBound

theorem coord_sq_le {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (hc : 0 < c)
    (hY : ∀ x : Fin g → ℝ, c * ∑ l, x l ^ 2 ≤ MCSchur.qf Y x) (β : Fin g → ℝ) (k : Fin g) :
    c * β k ^ 2 ≤ MCSchur.qf Y β := by
  have h1 : β k ^ 2 ≤ ∑ l, β l ^ 2 :=
    Finset.single_le_sum (f := fun l => β l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  nlinarith [hY β]

theorem mulVec_sq_le {g : ℕ} (X : Matrix (Fin g) (Fin g) ℝ) (M : ℝ) (k : Fin g)
    (hX : ∀ l, |X k l| ≤ M) (β : Fin g → ℝ) :
    (X *ᵥ β) k ^ 2 ≤ g * M ^ 2 * ∑ l, β l ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => X k l) β
  have hrow : ∑ l, X k l ^ 2 ≤ g * M ^ 2 := by
    calc ∑ l, X k l ^ 2 ≤ ∑ _l : Fin g, M ^ 2 := Finset.sum_le_sum fun l _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hX l) 2
      _ = g * M ^ 2 := by simp
  have hb : 0 ≤ ∑ l, β l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have he : (X *ᵥ β) k = ∑ l, X k l * β l := rfl
  rw [he]
  calc _ ≤ (∑ l, X k l ^ 2) * ∑ l, β l ^ 2 := hcs
    _ ≤ g * M ^ 2 * ∑ l, β l ^ 2 := mul_le_mul_of_nonneg_right hrow hb

end CuspCoordinateBound

theorem CuspCoordinateBound.proof (hImPos : ChartPeriodImPos.Statement)
    (hLow : ChartLowerBlockBound.Statement) (hPG : PeriodGramPosDef.Statement) :
    CuspCoordinateBound.Statement := by
  intro D T
  obtain ⟨M, hM, hMb⟩ := hLow D T
  have hc : 0 < D.c := D.c_pos
  set K : ℝ := 1 / D.c + 2 * M + 2 * D.g * M ^ 2 / D.c with hK
  have hK1 : 0 ≤ 1 / D.c := by positivity
  have hK2 : 0 ≤ 2 * (D.g : ℝ) * M ^ 2 / D.c := by positivity
  have hKpos : 0 < K := by positivity
  refine ⟨1 / K, by positivity, ?_⟩
  intro p hp hpU ℓ hℓ y i hi
  obtain ⟨hYpd, hYc⟩ := hImPos D p.1 hpU ℓ hℓ
  set τ := D.period p.1 ℓ with hτ
  set Y := τ.map Complex.im with hYdef
  set X := τ.map Complex.re with hXdef
  obtain ⟨-, hform⟩ := hPG D.g τ hYpd
  set α : Fin D.g → ℝ := fun k => y (Fin.castAdd D.g k) with hα
  set β : Fin D.g → ℝ := fun k => y (Fin.natAdd D.g k) with hβ
  have hA : 0 ≤ MCSchur.qf Y⁻¹ (α + X *ᵥ β) := MCCusp.qf_nonneg hYpd.inv.posSemidef _
  have hB : 0 ≤ MCSchur.qf Y β := MCCusp.qf_nonneg hYpd.posSemidef _
  suffices h : y i ^ 2 ≤ K * MCSchur.qf (periodGram τ) y by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hKpos]
    linarith
  rw [hform y]
  by_cases hig : i.val < D.g
  · set k : Fin D.g := ⟨i.val, hig⟩ with hkdef
    have hik : i = Fin.castAdd D.g k := Fin.ext rfl
    have hkr : T.r ≤ k.val := hi
    have hyk : y i = α k := congrArg y hik
    have hYkk : Y k k ≤ M :=
      calc Y k k = (τ k k).im := rfl
        _ ≤ |(τ k k).im| := le_abs_self _
        _ ≤ ‖τ k k‖ := Complex.abs_im_le_norm _
        _ ≤ M := hMb p hp ℓ k k hkr
    have hXk : ∀ l, |X k l| ≤ M := fun l =>
      (Complex.abs_re_le_norm _).trans (hMb p hp ℓ k l hkr)
    have hu : (α + X *ᵥ β) k ^ 2 ≤ M * MCSchur.qf Y⁻¹ (α + X *ᵥ β) := by
      have h1 := MCCusp.sq_le_inv_diag_mul_qf hYpd.inv (α + X *ᵥ β) k
      rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hYpd.isUnit)]
        at h1
      exact h1.trans (mul_le_mul_of_nonneg_right hYkk hA)
    have hw := CuspCoordinateBound.mulVec_sq_le X M k hXk β
    have hsplit : α k = (α + X *ᵥ β) k - (X *ᵥ β) k := by simp
    have hw2 : (X *ᵥ β) k ^ 2 ≤ D.g * M ^ 2 / D.c * MCSchur.qf Y β := by
      refine hw.trans ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have h0 : 0 ≤ (D.g : ℝ) * M ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (hYc β) h0]
    rw [hyk, hsplit]
    have hab : ((α + X *ᵥ β) k - (X *ᵥ β) k) ^ 2 ≤
        2 * (α + X *ᵥ β) k ^ 2 + 2 * (X *ᵥ β) k ^ 2 := by
      nlinarith [sq_nonneg ((α + X *ᵥ β) k + (X *ᵥ β) k)]
    have hid : K * (MCSchur.qf Y⁻¹ (α + X *ᵥ β) + MCSchur.qf Y β) =
        2 * M * MCSchur.qf Y⁻¹ (α + X *ᵥ β) + 2 * (D.g * M ^ 2 / D.c) * MCSchur.qf Y β +
          (1 / D.c * MCSchur.qf Y⁻¹ (α + X *ᵥ β) + 1 / D.c * MCSchur.qf Y β +
            2 * D.g * M ^ 2 / D.c * MCSchur.qf Y⁻¹ (α + X *ᵥ β) + 2 * M * MCSchur.qf Y β) := by
      rw [hK]; ring
    have hM2 : 0 ≤ 2 * M := by positivity
    rw [hid]
    nlinarith [mul_nonneg hK1 hA, mul_nonneg hK1 hB, mul_nonneg hK2 hA, mul_nonneg hM2 hB]
  · set k : Fin D.g := ⟨i.val - D.g, by omega⟩ with hkdef
    have hik : i = Fin.natAdd D.g k := Fin.ext (by simp [hkdef]; omega)
    have hyk : y i = β k := congrArg y hik
    have h1 := CuspCoordinateBound.coord_sq_le Y D.c hc hYc β k
    have h2 : β k ^ 2 ≤ 1 / D.c * MCSchur.qf Y β := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
      linarith
    have hid : K * (MCSchur.qf Y⁻¹ (α + X *ᵥ β) + MCSchur.qf Y β) =
        1 / D.c * MCSchur.qf Y β + (K * MCSchur.qf Y⁻¹ (α + X *ᵥ β) +
          (2 * M + 2 * D.g * M ^ 2 / D.c) * MCSchur.qf Y β) := by
      rw [hK]; ring
    have hM2 : 0 ≤ 2 * M + 2 * D.g * M ^ 2 / D.c := by positivity
    rw [hyk, hid]
    nlinarith [mul_nonneg hKpos.le hA, mul_nonneg hM2 hB]

end

end GroundTheory.Heights₂.Heights
