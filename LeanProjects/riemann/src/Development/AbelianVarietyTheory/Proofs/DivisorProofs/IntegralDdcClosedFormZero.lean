import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormDbarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelMulOfDelEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormSmulDelSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelChartSupportedMulFormEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSumStatement

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxFormStokes

theorem integral_ddc_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (η Z : A.Fld), A.IsForm η → A.IsForm Z → A.del Z = 0 →
    A.dbar Z = 0 → A.integral (A.ddc η * Z) = 0 := by
  intro M _ _ _ _ _ _ n A η Z hη hZ hdZ _
  have hdη := GlobalTheory.T.isForm_dbar' A η hη
  have hγ := GlobalTheory.T.isForm_mul_of_isForm_of_isForm A _ _ hdη hZ
  obtain ⟨hγ', hdel⟩ := GlobalTheory.T.isForm_smul_del_smul A GlobalTheory.HermFrame.kappa _ hγ
  have e1 : A.ddc η * Z = A.del (GlobalTheory.HermFrame.kappa • (A.dbar η * Z)) := by
    rw [hdel, GlobalTheory.T.del_mul_of_del_eq_zero' A _ _ hdη hZ hdZ, GlobalTheory.CxForm.HolAtlas.ddc, smul_mul_assoc]
  rw [e1]
  set γ := GlobalTheory.HermFrame.kappa • (A.dbar η * Z)
  obtain ⟨N, c, χ, hχs, hχt, hχ1⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * γ) := fun j => GlobalTheory.T.isForm_mul_of_isForm_of_isForm A _ _ (A.isForm_fn (hχs j)) hγ'
  have hsum : γ = ∑ j, A.fn (χ j) * γ := by
    rw [← Finset.sum_mul]
    funext x
    simp only [Finset.sum_apply, Pi.mul_apply, GlobalTheory.CxForm.HolAtlas.fn, ← map_sum]
    rw [show (∑ j, ((χ j x.pt : ℝ) : ℂ)) = 1 by exact_mod_cast hχ1 x.pt, map_one, one_mul]
  rw [hsum, GlobalTheory.T.holAtlas_del_finset_sum A _ hf, GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ fun j => GlobalTheory.T.holAtlas_isForm_del A _ (hf j)]
  exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero A γ (χ j) (c j) hγ' (hχs j) (hχt j)

end GlobalTheory.CxFormStokes
