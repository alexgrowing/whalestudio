import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.PushFam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

lemma decay_comp_of_norm_le (g : E → ℂ) (k : ℕ) (C : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) (K : ℝ) :
    ∃ C' : ℝ, ∀ x y : E, ‖y‖ ≤ K * ‖x‖ → ‖g x‖ ≤ C' * (1 + ‖y‖) ^ (-(k : ℝ)) := by
  refine ⟨max C 0 * (1 + |K|) ^ k, fun x y hxy => ?_⟩
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have h2 : 1 + ‖y‖ ≤ (1 + |K|) * (1 + ‖x‖) := by
    have h3 : K * ‖x‖ ≤ |K| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self K) hx
    have h4 : 0 ≤ |K| := abs_nonneg K
    nlinarith
  have h3 : (1 + ‖x‖) ^ (-(k : ℝ)) ≤ (1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
      Real.rpow_natCast, ← div_eq_mul_inv, inv_eq_one_div,
      div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc (1 + ‖y‖) ^ k ≤ ((1 + |K|) * (1 + ‖x‖)) ^ k := pow_le_pow_left₀ (by positivity) h2 k
      _ = (1 + |K|) ^ k * (1 + ‖x‖) ^ k := mul_pow _ _ _
  calc ‖g x‖ ≤ C * (1 + ‖x‖) ^ (-(k : ℝ)) := hC x
    _ ≤ max C 0 * (1 + ‖x‖) ^ (-(k : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ((1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
    _ = max C 0 * (1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ)) := by ring

theorem integrable_continuousAt_clm_comp (m : Measure E) (k : ℕ)
    (hW : Integrable (fun y : E => (1 + ‖y‖) ^ (-(k : ℝ))) m)
    (g : E → ℂ) (hg : Continuous g) (C : ℝ) (hC : ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)))
    (A₀ : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) (hA₀ : ∀ y, ‖y‖ ≤ M * ‖A₀ y‖) :
    (∀ᶠ A in 𝓝 A₀, Integrable (fun y => g (A y)) m) ∧
      ContinuousAt (fun A : E →L[ℝ] E => ∫ y, g (A y) ∂m) A₀ := by
  have hev : ∀ᶠ A in 𝓝 A₀, ∀ y, ‖y‖ ≤ (2 * M) * ‖A y‖ := by
    filter_upwards [Metric.ball_mem_nhds A₀ (show (0 : ℝ) < 1 / (2 * M) by positivity)] with A hA y
    rw [Metric.mem_ball, dist_eq_norm] at hA
    have e1 : A₀ y = A y - (A - A₀) y := by simp
    have h2 : ‖A₀ y‖ ≤ ‖A y‖ + 1 / (2 * M) * ‖y‖ := by
      calc ‖A₀ y‖ = ‖A y - (A - A₀) y‖ := by rw [← e1]
        _ ≤ ‖A y‖ + ‖(A - A₀) y‖ := norm_sub_le _ _
        _ ≤ ‖A y‖ + ‖A - A₀‖ * ‖y‖ := by gcongr; exact (A - A₀).le_opNorm y
        _ ≤ ‖A y‖ + 1 / (2 * M) * ‖y‖ := by
            gcongr
    have h3 : M * (1 / (2 * M) * ‖y‖) = ‖y‖ / 2 := by field_simp
    have h4 := hA₀ y
    have h5 : M * ‖A₀ y‖ ≤ M * ‖A y‖ + ‖y‖ / 2 := by
      rw [← h3, ← mul_add]; exact mul_le_mul_of_nonneg_left h2 hM.le
    linarith
  obtain ⟨C', hC'⟩ := decay_comp_of_norm_le g k C hC (2 * M)
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with A hA
    exact (hW.const_mul C').mono' (hg.comp A.continuous).aestronglyMeasurable
      (ae_of_all _ fun y => hC' _ _ (hA y))
  · refine tendsto_integral_filter_of_dominated_convergence
      (fun y => C' * (1 + ‖y‖) ^ (-(k : ℝ))) ?_ ?_ (hW.const_mul C') (ae_of_all _ fun y => ?_)
    · exact Eventually.of_forall fun A => (hg.comp A.continuous).aestronglyMeasurable
    · filter_upwards [hev] with A hA
      exact ae_of_all _ fun y => hC' _ _ (hA y)
    · exact (hg.comp (continuous_id.clm_apply continuous_const)).continuousAt.tendsto

end GlobalTheory.CompanionTheory.PushFam

namespace GlobalTheory.CompanionTheory.PushFam

theorem integrable_continuousAt_of_linear_push : PositivityTheory.PfSWUS.SchInf.FamCont := by
  intro N X _ μ' hμ' n c O hO hcO hfin hL g hg hdecay
  haveI := hμ'
  set k : ℕ := N + 1 with hk
  set W : (Fin N → ℝ) → ℝ := fun y => (1 + ‖y‖) ^ (-(k : ℝ)) with hWdef
  have hWnonneg : ∀ y, 0 ≤ W y := fun y => by positivity
  have hWμ : Integrable W μ' :=
    integrable_one_add_norm (by rw [Module.finrank_fin_fun, hk]; push_cast; linarith)
  have hWmeas : Measurable W := (measurable_const.add measurable_norm).pow_const _
  obtain ⟨s0, hs0O, hs0fin⟩ := hfin (fun y => ENNReal.ofReal (W y))
    (ENNReal.measurable_ofReal.comp hWmeas)
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hWnonneg)).1 hWμ.2).ne O hO ⟨c, hcO⟩
  have hWm : Integrable W (n s0) := ⟨hWmeas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hWnonneg)).2 (lt_top_iff_ne_top.2 hs0fin)⟩
  obtain ⟨L, Linv, Λ, hLc, _hLinvc, hΛc, hinv, hpush⟩ := hL s0 hs0O
  obtain ⟨C, hC⟩ := hdecay k
  have hA₀ : ∀ y, ‖y‖ ≤ (‖Linv c‖ + 1) * ‖L c y‖ := fun y => by
    calc ‖y‖ = ‖Linv c (L c y)‖ := by rw [hinv c hcO]
      _ ≤ ‖Linv c‖ * ‖L c y‖ := (Linv c).le_opNorm _
      _ ≤ (‖Linv c‖ + 1) * ‖L c y‖ := by gcongr; linarith
  obtain ⟨hint, hcont⟩ := integrable_continuousAt_clm_comp (n s0) k hWm g hg C hC (L c)
    (‖Linv c‖ + 1) (by positivity) hA₀
  have hint' : ∀ᶠ s in 𝓝 c, Integrable (fun y => g (L s y)) (n s0) := hLc.eventually hint
  have hO' : O ∈ 𝓝 c := hO.mem_nhds hcO
  refine ⟨?_, ?_⟩
  · filter_upwards [hint', hO'] with s hs hsO
    rw [hpush s hsO]
    exact ((integrable_map_measure hg.aestronglyMeasurable
      (L s).continuous.aemeasurable).2 hs).smul_measure_nnreal
  · have hH : ContinuousAt (fun s => (Λ s : ℝ) • ∫ y, g (L s y) ∂(n s0)) c :=
      (NNReal.continuous_coe.continuousAt.comp hΛc).smul
        (ContinuousAt.comp (f := L) (g := fun A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) =>
          ∫ y, g (A y) ∂(n s0)) hcont hLc)
    refine hH.congr ?_
    filter_upwards [hO'] with s hs
    rw [hpush s hs, integral_smul_nnreal_measure,
      integral_map (L s).continuous.aemeasurable hg.aestronglyMeasurable, NNReal.smul_def]

end GlobalTheory.CompanionTheory.PushFam
