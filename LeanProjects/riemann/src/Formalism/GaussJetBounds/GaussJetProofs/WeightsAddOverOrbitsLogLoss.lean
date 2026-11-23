import Formalism.GaussJetBounds.StatementO
import Formalism.GaussJetBounds.OneLetterRadius
import Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight
import Formalism.GaussJetBounds.GaussJetProofs.LemmaRA
import Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbits

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem unipotent_weight_bound : UWt.{u, v, w} := by
  classical
  intro K _ _ _ l hl hpi τ _ _ p g hg0 hg U hU ι _ M hM1 sig hsig
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hpi.le
  have hrho : 0 ≤ rho l := by
    unfold rho
    apply div_nonneg zero_le_one
    nlinarith
  have hr : ∀ i, (fun _ : ι => rho l) i ≤ (fun i => rho l + sig i) i := fun i => by
    simp only
    linarith [hsig i]
  have hlin0 : ∀ x, MvPowerSeries.constantCoeff
      (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by
    intro x
    simp
  have hU0 : WtGe ‖(l : K)‖ (fun _ : τ => rho l) 0 U := by
    intro n
    rw [monoWtGe_iff]
    refine le_trans (hU n) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 ?_)
    linarith [asmR_dot_nonneg n (r := fun _ : τ => rho l) fun _ => hrho]
  have hgw := generalized_log_weight K l hl hpi τ p g hg0 hg
  have hgU : WtGe ‖(l : K)‖ (fun _ : τ => rho l) 0 (MvPowerSeries.subst g U) :=
    substitution_weight_bound K ‖(l : K)‖ h0 hpi τ τ g (fun _ => rho l) (fun _ => rho l) 0 U hg0 hgw hU0
  have hlinw : ∀ x, WtGe ‖(l : K)‖ (fun _ : ι => rho l) (rho l)
      (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i : MvPowerSeries ι K) := by
    intro x n
    rw [monoWtGe_iff]
    simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
      fun i _ => ?_
    split_ifs with h
    · subst h
      rw [mul_one, asmR_dot_single]
      simpa using hM1 x i
    · simpa using Real.rpow_nonneg h0.le _
  have hY : WtGe ‖(l : K)‖ (fun _ : ι => rho l) 0
      (MvPowerSeries.subst (fun x => (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i :
        MvPowerSeries ι K)) (MvPowerSeries.subst g U)) :=
    substitution_weight_bound K ‖(l : K)‖ h0 hpi τ ι _ (fun _ => rho l) (fun _ => rho l) 0 _
      hlin0 hlinw hgU
  exact (radical_weight_monotone K ‖(l : K)‖ h0 hpi ι (fun _ => rho l) (fun i => rho l + sig i) 0 hr).1 _ hY

theorem lemma_R_core_log_loss : RCoreA.{u, v} := by
  intro K _ _ _ l hl hpi ι _ sig κ a ha hκa B U hB0 hB hU
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have hrg : gam l = 1 / ((l : ℝ) - 1) - rho l := by
    have ha : (l : ℝ) - 1 ≠ 0 := by linarith
    have hb : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    unfold gam rho
    field_simp
    ring
  have hExp := exponential_weight_le K l hl hpi ι (fun i => rho l + sig i) κ B hB0 hB
  have hk := multiplicative_weight_le K ‖(l : K)‖ h0 ι (fun i => rho l + sig i) 0 0 κ U (mvExp B) hU hExp
    κ le_rfl
  rw [monoWtGe_iff] at hk
  have hf := factValA (K := K) hl hpi κ ha hκa
  rw [norm_mul]
  calc _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) *
        ‖(l : K)‖ ^ (0 + 0 - dot κ (fun i => rho l + sig i)) :=
        mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = _ := by
      rw [← Real.rpow_add h0]
      congr 1
      rw [coreL_dot_fintype, hrg]
      have key : ∑ i, (κ i : ℝ) * (1 / ((l : ℝ) - 1) - rho l - sig i) =
          (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * (rho l + sig i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith

end Formalism.DworkPowerSeriesWeights
