import Mathlib

open MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.Conv

lemma fatou_real {α : Type} [MeasurableSpace α] {ν : Measure α} {g : ℕ → α → ℝ} {g0 : α → ℝ}
    {c : ℝ} (hi : ∀ k, Integrable (g k) ν) (hnn : ∀ k, ∀ᵐ y ∂ν, 0 ≤ g k y)
    (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => g k y) atTop (𝓝 (g0 y)))
    (hc : ∀ k, ∫ y, g k y ∂ν ≤ c) :
    Integrable g0 ν ∧ ∫ y, g0 y ∂ν ≤ c := by
  have hm : AEStronglyMeasurable g0 ν :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hi k).aestronglyMeasurable) hlim
  have hnn0 : ∀ᵐ y ∂ν, 0 ≤ g0 y := by
    filter_upwards [ae_all_iff.2 hnn, hlim] with y h1 h2
    exact ge_of_tendsto' h2 h1
  have hc0 : 0 ≤ c := (integral_nonneg_of_ae (hnn 0)).trans (hc 0)
  have hk : ∀ k, ∫⁻ y, ENNReal.ofReal (g k y) ∂ν ≤ ENNReal.ofReal c := fun k => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi k) (hnn k)]
    exact ENNReal.ofReal_le_ofReal (hc k)
  have hle : ∫⁻ y, ENNReal.ofReal (g0 y) ∂ν ≤ ENNReal.ofReal c := by
    calc ∫⁻ y, ENNReal.ofReal (g0 y) ∂ν
        = ∫⁻ y, liminf (fun k => ENNReal.ofReal (g k y)) atTop ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hlim] with y hy
          exact ((ENNReal.continuous_ofReal.tendsto _).comp hy).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ y, ENNReal.ofReal (g k y) ∂ν) atTop :=
          lintegral_liminf_le' (fun k => (hi k).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal c := liminf_le_of_frequently_le' (Frequently.of_forall hk)
  have hint : Integrable g0 ν :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal hnn0).2 (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have := hle
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn0] at this
  exact (ENNReal.ofReal_le_ofReal_iff hc0).1 this

lemma tail_bound {α : Type} [MeasurableSpace α] {μ : Measure α} {S E0 : Set α}
    (hS : MeasurableSet S) (hSE : S ⊆ E0ᶜ) {L ρ Γ : α → ℝ} {a c : ℝ} (ha : 0 ≤ a)
    (hρm : AEStronglyMeasurable ρ μ) (hΓm : AEStronglyMeasurable Γ μ)
    (hρ : ∀ᵐ y ∂μ, 0 ≤ ρ y) (hΓ : ∀ᵐ y ∂μ, y ∉ E0 → |Γ y| ≤ a * L y)
    (hi : IntegrableOn (fun y => L y * ρ y) S μ) (hc : ∫ y in S, L y * ρ y ∂μ ≤ c) :
    IntegrableOn (fun y => Γ y * ρ y) S μ ∧ |∫ y in S, Γ y * ρ y ∂μ| ≤ a * c := by
  have hb : ∀ᵐ y ∂μ.restrict S, ‖Γ y * ρ y‖ ≤ a * (L y * ρ y) := by
    rw [ae_restrict_iff' hS]
    filter_upwards [hρ, hΓ] with y h1 h2 hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (h2 (hSE hy)) h1
  have hi' : Integrable (fun y => a * (L y * ρ y)) (μ.restrict S) := Integrable.const_mul hi a
  refine ⟨Integrable.mono' hi' (hΓm.mul hρm).restrict hb, ?_⟩
  calc |∫ y in S, Γ y * ρ y ∂μ| = ‖∫ y in S, Γ y * ρ y ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y in S, a * (L y * ρ y) ∂μ := norm_integral_le_of_norm_le hi' hb
    _ = a * ∫ y in S, L y * ρ y ∂μ := integral_const_mul _ _
    _ ≤ a * c := mul_le_mul_of_nonneg_left hc ha

theorem tendsto_integral_of_exhaustion {α : Type} [MeasurableSpace α] (μ : Measure α)
    (l : Filter ℝ) [l.NeBot] [l.IsCountablyGenerated] (E : ℕ → Set α) (L : α → ℝ)
    (ρ Γ : ℝ → α → ℝ) (ρ0 Γ0 : α → ℝ) (a : ℝ) (b : ℕ → ℝ)
    (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E) (hfin : ∀ n, μ (E n) < ⊤)
    (hcov : ∀ᵐ y ∂μ, ∃ n, y ∈ E n) (hL : ∀ᵐ y ∂μ, 0 ≤ L y) (ha : 0 ≤ a)
    (hb : Tendsto b atTop (𝓝 0))
    (hρ : ∀ n, TendstoUniformlyOn ρ ρ0 l (E n)) (hΓ : ∀ n, TendstoUniformlyOn Γ Γ0 l (E n))
    (hM : ∀ n, ∃ M : ℝ, ∀ y ∈ E n, |ρ0 y| ≤ M ∧ |Γ0 y| ≤ M)
    (hev : ∀ᶠ t in l, AEStronglyMeasurable (ρ t) μ ∧ AEStronglyMeasurable (Γ t) μ ∧
      (∀ᵐ y ∂μ, 0 ≤ ρ t y) ∧ (∀ᵐ y ∂μ, y ∉ E 0 → |Γ t y| ≤ a * L y) ∧
      ∀ n, IntegrableOn (fun y => L y * ρ t y) (E n)ᶜ μ ∧ ∫ y in (E n)ᶜ, L y * ρ t y ∂μ ≤ b n) :
    Integrable (fun y => Γ0 y * ρ0 y) μ ∧ (∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ) ∧
      Tendsto (fun t => ∫ y, Γ t y * ρ t y ∂μ) l (𝓝 (∫ y, Γ0 y * ρ0 y ∂μ)) := by
  obtain ⟨u, hu⟩ := exists_seq_tendsto l
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hu.eventually hev)
  have hv : Tendsto (fun k => u (k + K)) atTop l := (tendsto_add_atTop_iff_nat K).2 hu
  have hG := fun k => hK (k + K) (Nat.le_add_left K k)
  have hpt : ∀ᵐ y ∂μ, Tendsto (fun k => ρ (u (k + K)) y) atTop (𝓝 (ρ0 y)) ∧
      Tendsto (fun k => Γ (u (k + K)) y) atTop (𝓝 (Γ0 y)) := by
    filter_upwards [hcov] with y hy
    obtain ⟨n, hn⟩ := hy
    exact ⟨((hρ n).tendsto_at hn).comp hv, ((hΓ n).tendsto_at hn).comp hv⟩
  have hρ0m : AEStronglyMeasurable ρ0 μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).1) (hpt.mono fun _ h => h.1)
  have hΓ0m : AEStronglyMeasurable Γ0 μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).2.1) (hpt.mono fun _ h => h.2)
  have hρ0nn : ∀ᵐ y ∂μ, 0 ≤ ρ0 y := by
    filter_upwards [ae_all_iff.2 (fun k => (hG k).2.2.1), hpt] with y h1 h2
    exact ge_of_tendsto' h2.1 h1
  have hΓ0b : ∀ᵐ y ∂μ, y ∉ E 0 → |Γ0 y| ≤ a * L y := by
    filter_upwards [ae_all_iff.2 (fun k => (hG k).2.2.2.1), hpt] with y h1 h2 hy
    exact le_of_tendsto' h2.2.abs (fun k => h1 k hy)
  have htail0 : ∀ n, IntegrableOn (fun y => L y * ρ0 y) (E n)ᶜ μ ∧
      ∫ y in (E n)ᶜ, L y * ρ0 y ∂μ ≤ b n := fun n =>
    fatou_real (g := fun k y => L y * ρ (u (k + K)) y)
      (fun k => ((hG k).2.2.2.2 n).1)
      (fun k => ae_restrict_of_ae (by
        filter_upwards [hL, (hG k).2.2.1] with y h1 h2
        exact mul_nonneg h1 h2))
      (ae_restrict_of_ae (by
        filter_upwards [hpt] with y h
        exact h.1.const_mul (L y)))
      (fun k => ((hG k).2.2.2.2 n).2)
  have hsub : ∀ n, (E n)ᶜ ⊆ (E 0)ᶜ := fun n =>
    Set.compl_subset_compl.2 (hmono (Nat.zero_le n))
  have htailLim : ∀ n, IntegrableOn (fun y => Γ0 y * ρ0 y) (E n)ᶜ μ ∧
      |∫ y in (E n)ᶜ, Γ0 y * ρ0 y ∂μ| ≤ a * b n := fun n =>
    tail_bound (hEm n).compl (hsub n) ha hρ0m hΓ0m hρ0nn hΓ0b (htail0 n).1 (htail0 n).2
  have htailT : ∀ᶠ t in l, ∀ n, IntegrableOn (fun y => Γ t y * ρ t y) (E n)ᶜ μ ∧
      |∫ y in (E n)ᶜ, Γ t y * ρ t y ∂μ| ≤ a * b n := hev.mono fun t h n =>
    tail_bound (hEm n).compl (hsub n) ha h.1 h.2.1 h.2.2.1 h.2.2.2.1
      (h.2.2.2.2 n).1 (h.2.2.2.2 n).2
  have hB : ∀ n, ∃ C : ℝ, (∀ y ∈ E n, |Γ0 y * ρ0 y| ≤ C) ∧
      ∀ᶠ t in l, ∀ y ∈ E n, |Γ t y * ρ t y| ≤ C := by
    intro n
    obtain ⟨M, hM'⟩ := hM n
    have hC : (0 : ℝ) ≤ |M| + 1 := by positivity
    have key : ∀ x z : ℝ, |x| ≤ |M| + 1 → |z| ≤ |M| + 1 → |x * z| ≤ (|M| + 1) * (|M| + 1) := by
      intro x z h1 h2
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hC
    have near : ∀ x z : ℝ, |z| ≤ M → dist z x < 1 → |x| ≤ |M| + 1 := by
      intro x z h1 h2
      rw [Real.dist_eq] at h2
      have h3 := abs_sub_abs_le_abs_sub x z
      rw [abs_sub_comm x z] at h3
      have h4 := le_abs_self M
      linarith
    refine ⟨(|M| + 1) * (|M| + 1), fun y hy => ?_, ?_⟩
    · have h4 := le_abs_self M
      exact key _ _ (by linarith [(hM' y hy).2]) (by linarith [(hM' y hy).1])
    · filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hρ n) 1 one_pos,
        Metric.tendstoUniformlyOn_iff.1 (hΓ n) 1 one_pos] with t h1 h2 y hy
      exact key _ _ (near _ _ (hM' y hy).2 (h2 y hy)) (near _ _ (hM' y hy).1 (h1 y hy))
  have hhead0 : ∀ n, IntegrableOn (fun y => Γ0 y * ρ0 y) (E n) μ := by
    intro n
    obtain ⟨C, hC, -⟩ := hB n
    exact Measure.integrableOn_of_bounded (hfin n).ne (hΓ0m.mul hρ0m) (M := C)
      (ae_restrict_of_forall_mem (hEm n) hC)
  have hheadT : ∀ n, ∀ᶠ t in l, IntegrableOn (fun y => Γ t y * ρ t y) (E n) μ := by
    intro n
    obtain ⟨C, -, hC⟩ := hB n
    filter_upwards [hev, hC] with t h1 h2
    exact Measure.integrableOn_of_bounded (hfin n).ne (h1.2.1.mul h1.1) (M := C)
      (ae_restrict_of_forall_mem (hEm n) h2)
  have hU : ∀ f : α → ℝ, IntegrableOn f (E 0) μ → IntegrableOn f (E 0)ᶜ μ → Integrable f μ := by
    intro f h1 h2
    have := h1.union h2
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have hI0 : Integrable (fun y => Γ0 y * ρ0 y) μ := hU _ (hhead0 0) (htailLim 0).1
  have hIT : ∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ := by
    filter_upwards [htailT, hheadT 0] with t h1 h2
    exact hU _ h2 (h1 0).1
  refine ⟨hI0, hIT, ?_⟩
  have hconv : ∀ n, Tendsto (fun t => ∫ y in E n, Γ t y * ρ t y ∂μ) l
      (𝓝 (∫ y in E n, Γ0 y * ρ0 y ∂μ)) := by
    intro n
    obtain ⟨C, -, hC⟩ := hB n
    haveI : IsFiniteMeasure (μ.restrict (E n)) := ⟨by simpa using hfin n⟩
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
      (integrable_const C) ?_
    · exact hev.mono fun t h => (h.2.1.mul h.1).restrict
    · exact hC.mono fun t h => ae_restrict_of_forall_mem (hEm n) h
    · exact ae_restrict_of_forall_mem (hEm n) fun y hy =>
        ((hΓ n).tendsto_at hy).mul ((hρ n).tendsto_at hy)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hbn : Tendsto (fun n => a * |b n|) atTop (𝓝 0) := by
    simpa using hb.abs.const_mul a
  obtain ⟨n, hn⟩ := (hbn.eventually (Iio_mem_nhds hε3)).exists
  have hn' : a * |b n| < ε / 3 := hn
  have hab : a * b n ≤ a * |b n| := mul_le_mul_of_nonneg_left (le_abs_self _) ha
  filter_upwards [Metric.tendsto_nhds.1 (hconv n) (ε / 3) hε3, htailT, hIT] with t h1 h2 h3
  have e1 : ∫ y in E n, Γ t y * ρ t y ∂μ + ∫ y in (E n)ᶜ, Γ t y * ρ t y ∂μ =
      ∫ y, Γ t y * ρ t y ∂μ := integral_add_compl (hEm n) h3
  have e2 : ∫ y in E n, Γ0 y * ρ0 y ∂μ + ∫ y in (E n)ᶜ, Γ0 y * ρ0 y ∂μ =
      ∫ y, Γ0 y * ρ0 y ∂μ := integral_add_compl (hEm n) hI0
  have A := (h2 n).2
  have B := (htailLim n).2
  rw [Real.dist_eq] at h1 ⊢
  rw [← e1, ← e2]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at A B
  constructor <;> linarith [h1.1, h1.2, A.1, A.2, B.1, B.2]

end GlobalTheory.CompanionTheory.Conv
