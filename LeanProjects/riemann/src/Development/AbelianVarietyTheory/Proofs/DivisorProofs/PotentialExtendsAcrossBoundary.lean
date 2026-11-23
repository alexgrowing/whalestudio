import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereMeasureFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOnOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereDensityBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogSingularIntegrableDiscStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductIntegralFiniteStatement

namespace GlobalTheory.PoincareVolume

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

theorem maMeasure_compl_lt_top : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (P : LocPot X) {m : ℕ} (D : Fin m → Set X), IsOpen (⋃ i, D i)ᶜ → IsPotentialOn A (⋃ i, D i)ᶜ P → (∀ x : X, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsAdaptedPolydisc A D ψ σ ∧ x ∈ ψ.source ∧ ψ x = 0) → (∀ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsAdaptedPolydisc A D ψ σ → ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ψ.symm z ∉ ⋃ i, D i → ∀ w, C⁻¹ * modelAt σ z w ≤ formAt ψ P z w ∧ formAt ψ P z w ≤ C * modelAt σ z w) → maMeasure A (fun _ => P) (⋃ i, D i)ᶜ < ⊤ := by
  intro e X _ _ _ _ _ A P m D hO hP hcen hcmp
  classical
  apply GlobalTheory.T.monge_ampere_measure_finite A (fun _ => P) _ hO
  intro j x hx
  obtain ⟨ψ, σ, had, hxs, hx0⟩ := hcen x
  obtain ⟨ρ, hρ, C, hC, hbd⟩ := hcmp ψ σ had
  have hcompat : IsCompatChart A ψ := had.1
  have htgt : Metric.ball (0 : Fin e → ℂ) 1 ⊆ ψ.target := had.2.1
  have h0t : (0 : Fin e → ℂ) ∈ ψ.target := by rw [← hx0]; exact ψ.map_source hxs
  have hsym0 : ψ.symm 0 = x := by rw [← hx0]; exact ψ.left_inv hxs
  have hcont : ContinuousAt ψ.symm 0 := ψ.continuousAt_symm h0t
  obtain ⟨ε, hε, hεs⟩ : ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ε,
      ψ.symm z ∈ (A.chart j).source := by
    have hx' : ψ.symm 0 ∈ (A.chart j).source := by rw [hsym0]; exact hx
    have : ψ.symm ⁻¹' (A.chart j).source ∈ nhds (0 : Fin e → ℂ) :=
      hcont.preimage_mem_nhds ((A.chart j).open_source.mem_nhds hx')
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp this
    exact ⟨ε, hε, fun z hz => h hz⟩
  set r : ℝ := min (min ρ ε) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (lt_min hρ hε) (by norm_num)
  have hrρ : r ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
  have hr2 : r ≤ 1 / 2 := min_le_right _ _
  have hballt : Metric.ball (0 : Fin e → ℂ) r ⊆ ψ.target :=
    (Metric.ball_subset_ball (by linarith)).trans htgt
  have hballs : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, ψ.symm z ∈ (A.chart j).source :=
    fun z hz => hεs z (Metric.ball_subset_ball hrε hz)
  refine ⟨ψ.symm '' Metric.ball 0 r,
    ψ.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballt,
    ⟨0, Metric.mem_ball_self hr0, hsym0⟩, ?_⟩
  refine lt_of_le_of_lt (GlobalTheory.T.monge_ampere_local_integral A P _ ψ j r hO hP hcompat hballt hballs) ?_
  set B : Finset (Fin e) := Finset.univ.filter (fun k => ∃ i, σ i = some k) with hB
  set g : Fin e → ℂ → ℝ := fun k u => if k ∈ B then 1 / (‖u‖ ^ 2 * tOf u ^ 2) else 1 with hg
  have hg0 : ∀ k u, 0 ≤ g k u := by intro k u; simp only [hg]; split_ifs <;> positivity
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    by_cases hk : k ∈ B
    · simp only [hg, hk, if_true]
      unfold tOf
      fun_prop
    · simp only [hg, hk, if_false]
      exact measurable_const
  set K : ℝ := (e.factorial : ℝ) * C ^ e with hK
  have hpt : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' (⋃ i, D i)ᶜ,
      ENNReal.ofReal (maDens (fun _ => P.φ (ψ.symm z) ∘ ψ.symm) z) ≤
        ENNReal.ofReal K * ∏ k, ENNReal.ofReal (g k (z k)) := by
    rintro z ⟨hz, hzO⟩
    have hzρ : z ∈ Metric.ball (0 : Fin e → ℂ) ρ := Metric.ball_subset_ball hrρ hz
    have hb := hbd z hzρ hzO
    have hsm := GlobalTheory.T.potential_smooth_on_open A P _ ψ z hO hP hcompat (hballt hz) hzO
    have hmodel : ∀ w, modelAt σ z w = ∑ k, g k (z k) * ‖w k‖ ^ 2 := by
      intro w; unfold modelAt; refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hg, hB, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> first | ring | (exfalso; tauto)
    have hmodel0 : ∀ w, 0 ≤ modelAt σ z w := fun w => by
      rw [hmodel]; exact Finset.sum_nonneg fun k _ => mul_nonneg (hg0 k _) (by positivity)
    have hpi := Real.pi_pos
    have hlow : ∀ w, 0 ≤ levi (P.φ (ψ.symm z) ∘ ψ.symm) z w := by
      intro w
      have h2 : 0 ≤ formAt ψ P z w :=
        le_trans (mul_nonneg (inv_nonneg.2 hC.le) (hmodel0 w)) (hb w).1
      unfold formAt at h2
      exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h2
    have hup : ∀ w, levi (P.φ (ψ.symm z) ∘ ψ.symm) z w ≤
        ∑ k, (Real.pi / 2 * C * g k (z k)) * ‖w k‖ ^ 2 := by
      intro w
      have h1 := (hb w).2
      unfold formAt at h1
      rw [hmodel] at h1
      have hs : ∑ k, (Real.pi / 2 * C * g k (z k)) * ‖w k‖ ^ 2 =
          Real.pi / 2 * (C * ∑ k, g k (z k) * ‖w k‖ ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [hs]
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ Real.pi / 2)
      calc levi (P.φ (ψ.symm z) ∘ ψ.symm) z w
          = Real.pi / 2 * (2 / Real.pi * levi (P.φ (ψ.symm z) ∘ ψ.symm) z w) := by
            field_simp
        _ ≤ _ := h3
    have hdet := GlobalTheory.T.monge_ampere_density_bound _ z _ hsm hlow hup
    have hprod : (e.factorial : ℝ) * (2 / Real.pi) ^ e * ∏ k, (Real.pi / 2 * C * g k (z k)) =
        K * ∏ k, g k (z k) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hK,
        mul_pow]
      have h2 : (2 / Real.pi) ^ e * (Real.pi / 2) ^ e = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm 2 Real.pi, div_self (by positivity), one_pow]
      linear_combination ((e.factorial : ℝ) * C ^ e * ∏ k, g k (z k)) * h2
    rw [hprod] at hdet
    calc ENNReal.ofReal (maDens (fun _ => P.φ (ψ.symm z) ∘ ψ.symm) z)
        ≤ ENNReal.ofReal (K * ∏ k, g k (z k)) := ENNReal.ofReal_le_ofReal hdet
      _ = ENNReal.ofReal K * ∏ k, ENNReal.ofReal (g k (z k)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg (fun k _ => hg0 k _)]
  have hpm : Measurable fun z : Fin e → ℂ => ∏ k, ENNReal.ofReal (g k (z k)) :=
    Finset.measurable_prod _ fun k _ =>
      ENNReal.measurable_ofReal.comp ((hgm k).comp (measurable_pi_apply k))
  have hfin : ∀ k, ∫⁻ u in Metric.ball (0 : ℂ) r, ENNReal.ofReal (g k u) < ⊤ := by
    intro k
    by_cases hk : k ∈ B
    · simp only [hg, hk, if_true]
      exact GlobalTheory.T.log_singular_integrable_disc r hr2
    · simp only [hg, hk, if_false, ENNReal.ofReal_one, setLIntegral_const, one_mul]
      exact measure_ball_lt_top
  calc ∫⁻ z in Metric.ball 0 r ∩ ψ.symm ⁻¹' (⋃ i, D i)ᶜ,
        ENNReal.ofReal (maDens (fun _ => P.φ (ψ.symm z) ∘ ψ.symm) z)
      ≤ ∫⁻ z in Metric.ball 0 r ∩ ψ.symm ⁻¹' (⋃ i, D i)ᶜ,
        ENNReal.ofReal K * ∏ k, ENNReal.ofReal (g k (z k)) :=
        setLIntegral_mono (measurable_const.mul hpm) hpt
    _ ≤ ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r, ENNReal.ofReal K * ∏ k, ENNReal.ofReal (g k (z k)) :=
        lintegral_mono_set Set.inter_subset_left
    _ = ENNReal.ofReal K * ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r, ∏ k, ENNReal.ofReal (g k (z k)) :=
        lintegral_const_mul _ hpm
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (GlobalTheory.T.product_integral_finite r (fun k u => ENNReal.ofReal (g k u))
          (fun k => ENNReal.measurable_ofReal.comp (hgm k)) hfin)

end GlobalTheory.PoincareVolume
