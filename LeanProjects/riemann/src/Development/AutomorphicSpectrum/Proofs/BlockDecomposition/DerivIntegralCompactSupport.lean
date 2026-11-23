import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.IntDeriv

variable {n : ℕ}

theorem hasDerivAt_fderiv {ρ : ℝ → Mat n → ℝ} (h : Sm ρ) (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun r => ρ r y) (fderiv ℝ (Function.uncurry ρ) (s, y) (1, 0)) s := by
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod isOpen_GLs
  have hd : DifferentiableAt ℝ (Function.uncurry ρ) (s, y) :=
    ((h.contDiffAt (hopen.mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt (by simp))
  have hc : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : Mat n)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  have hd' : HasFDerivAt (Function.uncurry ρ) (fderiv ℝ (Function.uncurry ρ) (s, y))
      ((fun r : ℝ => (r, y)) s) := hd.hasFDerivAt
  exact hd'.comp_hasDerivAt s hc

theorem hasDerivAt_dt {ρ : ℝ → Mat n → ℝ} (h : Sm ρ) (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun r => ρ r y) (dt ρ s y) s := by
  have h2 := hasDerivAt_fderiv h s hy
  have : dt ρ s y = fderiv ℝ (Function.uncurry ρ) (s, y) (1, 0) := h2.deriv
  rw [this]; exact h2

theorem continuousOn_dt {ρ : ℝ → Mat n → ℝ} (h : Sm ρ) :
    ContinuousOn (Function.uncurry (dt ρ)) (Set.univ ×ˢ GLs n) := by
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod isOpen_GLs
  have hc : ContinuousOn (fderiv ℝ (Function.uncurry ρ)) (Set.univ ×ˢ GLs n) :=
    ContDiffOn.continuousOn_fderiv_of_isOpen h hopen (by simp)
  have h1 : ContinuousOn (fun p : ℝ × Mat n => fderiv ℝ (Function.uncurry ρ) p (1, 0))
      (Set.univ ×ˢ GLs n) := hc.clm_apply continuousOn_const
  refine h1.congr ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact (hasDerivAt_fderiv h s hy).deriv

theorem continuous_val_G : Continuous (fun y : G n => (y.val : Mat n)) := Units.continuous_val

theorem continuous_comp_val {W : Type} [TopologicalSpace W] {f : ℝ → Mat n → W}
    (h : ContinuousOn (Function.uncurry f) (Set.univ ×ˢ GLs n)) :
    Continuous (fun p : ℝ × G n => f p.1 p.2.val) := by
  have hm : Continuous (fun p : ℝ × G n => ((p.1, p.2.val) : ℝ × Mat n)) :=
    continuous_fst.prodMk (continuous_val_G.comp continuous_snd)
  exact h.comp_continuous hm (fun p => ⟨Set.mem_univ _, val_mem_GLs p.2⟩)

theorem hasDerivAt_integral_compact {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (ρ : ℝ → Mat n → ℝ) (hρ : Sm ρ) (K : Set (G n)) (hK : IsCompact K)
    (s₀ ε : ℝ) (hε : 0 < ε)
    (hv : ∀ s ∈ Metric.ball s₀ ε, ∀ y : G n, y ∉ K → ρ s y.val = 0) :
    HasDerivAt (fun s => ∫ y : G n, ρ s y.val ∂μ) (∫ y : G n, dt ρ s₀ y.val ∂μ) s₀ := by
  have hF : Continuous (fun p : ℝ × G n => ρ p.1 p.2.val) := continuous_comp_val hρ.continuousOn
  have hF' : Continuous (fun p : ℝ × G n => dt ρ p.1 p.2.val) :=
    continuous_comp_val (continuousOn_dt hρ)
  have hFs : ∀ s, Continuous (fun y : G n => ρ s y.val) := fun s =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hFs' : ∀ s, Continuous (fun y : G n => dt ρ s y.val) := fun s =>
    hF'.comp (continuous_const.prodMk continuous_id)
  have hKm : MeasurableSet K := hK.measurableSet
  have hv' : ∀ s ∈ Metric.ball s₀ ε, ∀ y : G n, y ∉ K → dt ρ s y.val = 0 := by
    intro s hs y hy
    have hev : (fun r => ρ r y.val) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hs] with r hr using hv r hr y hy
    have : dt ρ s y.val = deriv (fun r => ρ r y.val) s := rfl
    rw [this, hev.deriv_eq]; simp
  have hint : ∀ s ∈ Metric.ball s₀ ε, Integrable (fun y : G n => ρ s y.val) μ := by
    intro s hs
    refine (hFs s).integrable_of_hasCompactSupport (HasCompactSupport.intro hK ?_)
    exact fun y hy => hv s hs y hy
  have hint' : Integrable (fun y : G n => dt ρ s₀ y.val) μ := by
    refine (hFs' s₀).integrable_of_hasCompactSupport (HasCompactSupport.intro hK ?_)
    exact fun y hy => hv' s₀ (Metric.mem_ball_self hε) y hy
  have hs₀ : s₀ ∈ Metric.ball s₀ ε := Metric.mem_ball_self hε
  obtain ⟨M, hM⟩ := ((isCompact_closedBall s₀ (ε / 2)).prod hK).exists_bound_of_continuousOn
    hF'.continuousOn
  have hball : Metric.ball s₀ (ε / 2) ⊆ Metric.ball s₀ ε := Metric.ball_subset_ball (by linarith)
  have hbound : ∀ᵐ y ∂μ, ∀ s ∈ Metric.ball s₀ (ε / 2),
      ‖dt ρ s (y : G n).val‖ ≤ K.indicator (fun _ => M) y := by
    refine Filter.Eventually.of_forall fun y s hs => ?_
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      exact hM (s, y) ⟨Metric.ball_subset_closedBall hs, hy⟩
    · rw [Set.indicator_of_notMem hy, hv' s (hball hs) y hy]; simp
  have hbi : Integrable (K.indicator (fun _ : G n => M)) μ :=
    (integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s (y : G n) => ρ s y.val) (F' := fun s (y : G n) => dt ρ s y.val)
    (x₀ := s₀) (s := Metric.ball s₀ (ε / 2)) (bound := K.indicator (fun _ => M))
    (Metric.ball_mem_nhds s₀ (by linarith))
    (Filter.Eventually.of_forall fun s => (hFs s).aestronglyMeasurable)
    (hint s₀ hs₀) hint'.aestronglyMeasurable hbound hbi
    (Filter.Eventually.of_forall fun y s _ => hasDerivAt_dt hρ s (val_mem_GLs y))
  exact this.2

end GlobalTheory.CompanionTheory.WaveSpd.IntDeriv
