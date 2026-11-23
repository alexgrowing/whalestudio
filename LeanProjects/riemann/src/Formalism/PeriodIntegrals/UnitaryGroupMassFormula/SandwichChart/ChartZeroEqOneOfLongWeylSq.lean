import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare
import Formalism.PeriodIntegrals.SwSand
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SandwichOfOfCharts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.UnrealifyRL

set_option linter.unusedVariables false

noncomputable section

open Matrix Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSandwichOfWork

open PI.SwBig PI.SwSand

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

def PhiP (k r : ℕ) (p : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) : Mat k r :=
  Phi k r p.1 p.2.1 p.2.2.1 p.2.2.2

theorem Chart_tM_one : tM k r 1 = 1 := by
  have h : tv k r 1 = fun _ => 1 := by
    funext i
    unfold tv
    split_ifs <;> simp
  unfold tM
  rw [h, Matrix.diagonal_one]

theorem chart_zero_eq_one_of_longWeylSq (hW : LongWeylElementSquare) : PhiP k r 0 = 1 := by
  simp [PhiP, Phi, Chart_tM_one, hW k r]

theorem Chart_UH_mul {A B : Mat k r} (hA : A ∈ UH (Hpk k r)) (hB : B ∈ UH (Hpk k r)) :
    A * B ∈ UH (Hpk k r) := by
  have hA' : Aᴴ * Hpk k r * A = Hpk k r := hA
  have hB' : Bᴴ * Hpk k r * B = Hpk k r := hB
  show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
  rw [Matrix.conjTranspose_mul, show Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B by
    simp only [mul_assoc], hA', hB']

theorem Chart_phi_mem (hBC : BigCellG) (hPF : PhiForm) (hLW : LieWb) (hEN : ExpN)
    {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) (hx : ‖v.2.1‖ < 1) :
    PhiP k r v ∈ UH (Hpk k r) := by
  simp only [Vs, Submodule.mem_prod] at hv
  obtain ⟨h1, -, h3, h4⟩ := hv
  have hc : ∀ a, (1 + v.2.1) a ≠ 0 := by
    intro a h
    have h0 : (1 : ℂ) + v.2.1 a = 0 := h
    have h' : v.2.1 a = -1 := by linear_combination h0
    have hle := norm_le_pi_norm v.2.1 a
    rw [h', norm_neg, norm_one] at hle
    linarith
  have hw : w0B k r ∈ UH (Hpk k r) := hBC k r 1 (fun _ => by simp)
  obtain ⟨hX, -⟩ := hEN k r v.1 h1
  have hB : bigCell k r (1 + v.2.1) 1 ∈ UH (Hpk k r) := hBC k r _ hc
  obtain ⟨hZ, -⟩ := (hLW k r).1 _ h3
  have hX' : (NormedSpace.exp v.2.2.2)⁻¹ ∈ UH (Hpk k r) := by
    rw [← Matrix.exp_neg]
    obtain ⟨hm, -⟩ := hEN k r _ ((lieNS k r).neg_mem h4)
    exact hm
  have e := hPF k r v.1 v.2.1 v.2.2.1 v.2.2.2
  show Phi k r v.1 v.2.1 v.2.2.1 v.2.2.2 ∈ UH (Hpk k r)
  rw [e]
  exact Chart_UH_mul hw (Chart_UH_mul (Chart_UH_mul (Chart_UH_mul hX hB) hZ) hX')

private lemma le_of_sq_le_sq_of_nonneg_sandwich_chart {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

theorem Chart_norm_le (hN : NormRL) (hLI : LIso) {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r}
    (hv : v ∈ Vs k r) : ‖v‖ ≤ ‖Lm k r v‖ := by
  have h := (hLI k r).2.2 v hv
  simp only [hN k r] at h
  have hs : 0 ≤ ∑ a, ‖v.2.1 a‖ ^ 2 := Finset.sum_nonneg (fun a _ => by positivity)
  have hx1 : ‖v.2.1‖ ≤ Real.sqrt (∑ a, ‖v.2.1 a‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun a => ?_)
    calc ‖v.2.1 a‖ = Real.sqrt (‖v.2.1 a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ b, ‖v.2.1 b‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun b => ‖v.2.1 b‖ ^ 2)
          (fun b _ => by positivity) (Finset.mem_univ a))
  have hx : ‖v.2.1‖ ^ 2 ≤ ∑ a, ‖v.2.1 a‖ ^ 2 := by
    have hq := Real.sq_sqrt hs
    nlinarith [norm_nonneg v.2.1, Real.sqrt_nonneg (∑ a, ‖v.2.1 a‖ ^ 2)]
  have hL := norm_nonneg (Lm k r v)
  simp only [Prod.norm_def]
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_)) <;> refine le_of_sq_le_sq_of_nonneg_sandwich_chart (norm_nonneg _) hL ?_ <;>
    nlinarith [sq_nonneg ‖v.1‖, sq_nonneg ‖v.2.1‖, sq_nonneg ‖v.2.2.1‖, sq_nonneg ‖v.2.2.2‖]

theorem Chart_core (hN : NormRL) (hLog : LogG) (hW : LongWeylElementSquare) (hBC : BigCellG) (hPF : PhiForm)
    (hPD : PhiDeriv) (hLW : LieWb) (hEN : ExpN) (hLI : LIso) (k r : ℕ) :
    ∃ F : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r → Mat k r, HasStrictFDerivAt F (Lm k r) 0 ∧
      F 0 = 0 ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Vs k r, ‖v‖ < δ →
        F v ∈ uH k r ∧ NormedSpace.exp (F v) = PhiP k r v ∧ ‖F v - Lm k r v‖ ≤ η * ‖Lm k r v‖ := by
  have hE : HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r)
      ((ContinuousLinearEquiv.refl ℝ (Mat k r) : Mat k r ≃L[ℝ] Mat k r) : Mat k r →L[ℝ] Mat k r) 0 :=
    (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat k r)).congr_fderiv
      (ContinuousLinearMap.ext fun _ => rfl)
  set G := hE.localInverse _ _ _ with hGdef
  have hexp0 : NormedSpace.exp (0 : Mat k r) = 1 := by simp
  have hP : HasStrictFDerivAt (PhiP k r) (Lm k r) 0 := hPD k r
  have hPe : PhiP k r 0 = NormedSpace.exp (0 : Mat k r) := by rw [hexp0]; exact chart_zero_eq_one_of_longWeylSq hW
  have hF : HasStrictFDerivAt (fun v => G (PhiP k r v)) (Lm k r) 0 := by
    have h1 : HasStrictFDerivAt G
        (((ContinuousLinearEquiv.refl ℝ (Mat k r)).symm : Mat k r ≃L[ℝ] Mat k r) : Mat k r →L[ℝ] Mat k r)
        (PhiP k r 0) := by
      rw [hPe]; exact hE.to_localInverse
    exact (h1.comp 0 hP).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hF0 : G (PhiP k r 0) = 0 := by rw [hPe]; exact hE.localInverse_apply_image
  have hR : ∀ᶠ v in 𝓝 (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r),
      NormedSpace.exp (G (PhiP k r v)) = PhiP k r v := by
    have ht : Filter.Tendsto (PhiP k r) (𝓝 0) (𝓝 (NormedSpace.exp (0 : Mat k r))) := by
      rw [← hPe]; exact hP.continuousAt.tendsto
    exact ht.eventually hE.eventually_right_inverse
  obtain ⟨δL, hδL, hLg⟩ := hLog k r
  have hU : ∀ᶠ v in 𝓝 (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r), ‖G (PhiP k r v)‖ < δL := by
    have ht : Filter.Tendsto (fun v => G (PhiP k r v)) (𝓝 0) (𝓝 0) := by
      have h2 := hF.continuousAt.tendsto
      rwa [hF0] at h2
    exact (Metric.tendsto_nhds.mp ht δL hδL).mono fun v hv => by rwa [dist_zero_right] at hv
  have hB1 : ∀ᶠ v in 𝓝 (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r), ‖v‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) one_pos]
      with v hv
    exact mem_ball_zero_iff.mp hv
  refine ⟨fun v => G (PhiP k r v), hF, hF0, fun η hη => ?_⟩
  have hO : ∀ᶠ v in 𝓝 (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r),
      ‖G (PhiP k r v) - Lm k r v‖ ≤ η * ‖v‖ := by
    have h := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hF.hasFDerivAt).def hη
    filter_upwards [h] with v hv
    simp only [zero_add, hF0, sub_zero] at hv
    exact hv
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp (hR.and (hU.and (hB1.and hO)))
  refine ⟨δ, hδ, fun v hv hvn => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hall (show dist v 0 < δ by rwa [dist_zero_right])
  have hx : ‖v.2.1‖ < 1 := lt_of_le_of_lt ((norm_fst_le v.2).trans (norm_snd_le v)) h3
  refine ⟨hLg (G (PhiP k r v)) h2 (by rw [h1]; exact Chart_phi_mem hBC hPF hLW hEN hv hx), h1,
    h4.trans (mul_le_mul_of_nonneg_left (Chart_norm_le hN hLI hv) hη.le)⟩

theorem chartFwd : ChartFwdOf := by
  unfold ChartFwdOf ChartFwd
  intro hN hLog hW hBC hPF hPD hLW hEN hLI k r η hη
  obtain ⟨F, -, -, hFη⟩ := Chart_core hN hLog hW hBC hPF hPD hLW hEN hLI k r
  obtain ⟨δ, hδ, hδ'⟩ := hFη η hη
  refine ⟨δ, hδ, fun v hv hvn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hδ' v hv hvn
  refine ⟨F v, h1, h2, ?_⟩
  have h4 := norm_add_le (F v - Lm k r v) (Lm k r v)
  rw [sub_add_cancel] at h4
  nlinarith [h3, h4]

theorem chartBwd : ChartBwdOf := by
  unfold ChartBwdOf ChartBwd
  intro hN hLog hW hBC hPF hPD hLW hEN hLI k r η hη
  obtain ⟨F, hF, hF0, hFη⟩ := Chart_core hN hLog hW hBC hPF hPD hLW hEN hLI k r
  obtain ⟨δ1, hδ1, hδ1'⟩ := hFη η hη
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (uH k r)
  let pr : Mat k r →L[ℝ] uH k r :=
    LinearMap.toContinuousLinearMap ((uH k r).linearProjOfIsCompl q hq)
  have hpr : ∀ (Y : Mat k r) (hY : Y ∈ uH k r), pr Y = ⟨Y, hY⟩ := fun Y hY =>
    Submodule.linearProjOfIsCompl_apply_left hq ⟨Y, hY⟩
  set f : Vs k r → uH k r := fun w => pr (F w) with hfdef
  have hf : HasStrictFDerivAt f (pr.comp ((Lm k r).comp (Vs k r).subtypeL)) 0 := by
    have h1 : HasStrictFDerivAt F (Lm k r) ((Vs k r).subtypeL (0 : Vs k r)) := by
      rw [map_zero]; exact hF
    exact pr.hasStrictFDerivAt.comp (0 : Vs k r) (h1.comp (0 : Vs k r) (Vs k r).subtypeL.hasStrictFDerivAt)
  have hf0 : f 0 = 0 := by
    show pr (F ((0 : Vs k r) : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r)) = 0
    rw [Submodule.coe_zero, hF0, map_zero]
  have hmap := hf.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr fun y => by
    obtain ⟨v, hv, hLv⟩ := (hLI k r).2.1 y y.2
    refine ⟨⟨v, hv⟩, ?_⟩
    change pr (Lm k r v) = y
    rw [hLv, hpr _ y.2])
  rw [hf0] at hmap
  have hρ : 0 < min η δ1 := lt_min hη hδ1
  have hS : f '' Metric.ball (0 : Vs k r) (min η δ1) ∈ 𝓝 (0 : uH k r) :=
    (congrArg (fun l => f '' Metric.ball (0 : Vs k r) (min η δ1) ∈ l) hmap).mp
      (Filter.image_mem_map (Metric.ball_mem_nhds _ hρ))
  obtain ⟨δ2, hδ2, hball⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨δ2, hδ2, fun Y hY hYn => ?_⟩
  have hYb : (⟨Y, hY⟩ : uH k r) ∈ Metric.ball (0 : uH k r) δ2 := by
    rw [mem_ball_zero_iff]; exact hYn
  obtain ⟨⟨v, hv⟩, hwS, hfw⟩ := hball hYb
  have hvn : ‖v‖ < min η δ1 := mem_ball_zero_iff.mp hwS
  obtain ⟨h1, h2, h3⟩ := hδ1' v hv (lt_of_lt_of_le hvn (min_le_right _ _))
  have hFY : F v = Y := by
    have h : pr (F v) = ⟨Y, hY⟩ := hfw
    rw [hpr _ h1] at h
    exact congrArg Subtype.val h
  refine ⟨v, hv, ?_, lt_of_lt_of_le hvn (min_le_left _ _), ?_⟩
  · rw [← hFY]; exact h2.symm
  · have h4 := norm_sub_norm_le (Lm k r v) (F v)
    rw [norm_sub_rev, hFY] at h4
    rw [hFY] at h3
    nlinarith [h3, h4]

end PI.SwSandwichOfWork
