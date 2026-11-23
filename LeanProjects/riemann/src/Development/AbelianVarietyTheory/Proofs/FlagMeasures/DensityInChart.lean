import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDensityOriginOfAlmostHomogeneous
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.ChartDensity

section Meas
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem exists_eps_lt (n : ℕ) (s : ℝ) {a b : ℝ≥0∞} (hb : b ≠ ⊤) (h : a < b) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ a < b * ENNReal.ofReal ((1 + s * ε) ^ n) := by
  have t : Tendsto (fun ε : ℝ => b * ENNReal.ofReal ((1 + s * ε) ^ n)) (𝓝[>] 0)
      (𝓝 (b * ENNReal.ofReal ((1 + s * 0) ^ n))) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr hb)
    refine (Continuous.tendsto (f := fun ε : ℝ => ENNReal.ofReal ((1 + s * ε) ^ n)) ?_ 0).mono_left nhdsWithin_le_nhds
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  simp only [mul_zero, add_zero, one_pow, ENNReal.ofReal_one, mul_one] at t
  obtain ⟨ε, h1, h2⟩ := ((t.eventually (lt_mem_nhds h)).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  exact ⟨ε, h2.1, h2.2, h1⟩

theorem exists_eps_gt (n : ℕ) (s : ℝ) {a b : ℝ≥0∞} (h : b < a) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ b * ENNReal.ofReal ((1 + s * ε) ^ n) < a := by
  have t : Tendsto (fun ε : ℝ => b * ENNReal.ofReal ((1 + s * ε) ^ n)) (𝓝[>] 0)
      (𝓝 (b * ENNReal.ofReal ((1 + s * 0) ^ n))) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr h.ne_top)
    refine (Continuous.tendsto (f := fun ε : ℝ => ENNReal.ofReal ((1 + s * ε) ^ n)) ?_ 0).mono_left nhdsWithin_le_nhds
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  simp only [mul_zero, add_zero, one_pow, ENNReal.ofReal_one, mul_one] at t
  obtain ⟨ε, h1, h2⟩ := ((t.eventually (gt_mem_nhds h)).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  exact ⟨ε, h2.1, h2.2, h1⟩

theorem upper_of_density (l ν : Measure V) [l.IsAddHaarMeasure] [IsLocallyFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c))
    (H : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ → ∀ᶠ r in 𝓝[>] (0:ℝ),
      ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r))
    (t : NNReal) (ht : c < t) : ∃ δ : ℝ, 0 < δ ∧ ∀ A ⊆ Metric.ball (0 : V) δ, ν A ≤ t * l A := by
  obtain ⟨ε, h0, h1, hε⟩ := exists_eps_lt (Module.finrank ℝ V) (-1) ENNReal.coe_ne_top ht
  obtain ⟨δ, hδ, H⟩ := H (ε / 2) (by linarith) (by linarith)
  refine ⟨δ, hδ, fun A hA => ?_⟩
  have := (Besicovitch.vitaliFamily ν).measure_le_of_frequently_le (ρ := ν) (t • l)
    Measure.AbsolutelyContinuous.rfl A ?_
  · simpa using this
  intro x hx
  have hx' : ‖x‖ < δ := by simpa using hA hx
  have hs : 0 < 1 + -1 * ε := by linarith
  have ht := (Besicovitch.tendsto_filterAt ν x).comp (densHom_tendsto_mul hs)
  refine ht.frequently (Eventually.frequently ?_)
  filter_upwards [H x hx', self_mem_nhdsWithin, hc.eventually (gt_mem_nhds hε)] with r hr hr0 hlt
  have hr0 : 0 < r := hr0
  simp only [Function.comp, Measure.smul_apply]
  rw [densHom_scale l x hs hr0]
  have h2 : ν (Metric.closedBall x ((1 + -1 * ε) * r)) ≤ ν (Metric.ball 0 r) :=
    le_trans (measure_mono (Metric.closedBall_subset_ball (by nlinarith))) hr
  refine h2.trans ?_
  have h3 := (ENNReal.div_le_iff (Metric.measure_ball_pos l 0 hr0).ne' measure_ball_lt_top.ne).1 hlt.le
  rw [mul_assoc] at h3
  exact h3

theorem lower_of_density (l ν : Measure V) [l.IsAddHaarMeasure] [IsLocallyFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c))
    (H : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ → ∀ᶠ r in 𝓝[>] (0:ℝ),
      ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r)))
    (t : NNReal) (ht : (t : ℝ≥0∞) < c) : ∃ δ : ℝ, 0 < δ ∧ ∀ A ⊆ Metric.ball (0 : V) δ, t * l A ≤ ν A := by
  obtain ⟨ε, h0, h1, hε⟩ := exists_eps_gt (Module.finrank ℝ V) 1 ht
  obtain ⟨δ, hδ, H⟩ := H ε h0 h1
  refine ⟨δ, hδ, fun A hA => ?_⟩
  have := (Besicovitch.vitaliFamily l).measure_le_of_frequently_le (ρ := t • l) ν
    (Measure.AbsolutelyContinuous.rfl.smul_left _) A ?_
  · simpa using this
  intro x hx
  have hx' : ‖x‖ < δ := by simpa using hA hx
  have hs : 0 < 1 + 1 * ε := by linarith
  have ht := (Besicovitch.tendsto_filterAt l x).comp (densHom_tendsto_mul hs)
  refine ht.frequently (Eventually.frequently ?_)
  filter_upwards [H x hx', self_mem_nhdsWithin, hc.eventually (lt_mem_nhds hε)] with r hr hr0 hlt
  have hr0 : 0 < r := hr0
  simp only [Function.comp, Measure.smul_apply]
  rw [densHom_scale l x hs hr0]
  have h2 : ν (Metric.ball 0 r) ≤ ν (Metric.closedBall x ((1 + 1 * ε) * r)) :=
    le_trans hr (measure_mono (by rw [one_mul]; exact Metric.ball_subset_closedBall))
  refine le_trans ?_ h2
  have h3 := (ENNReal.le_div_iff_mul_le (Or.inl (Metric.measure_ball_pos l 0 hr0).ne') (Or.inl measure_ball_lt_top.ne)).1 hlt.le
  rw [mul_assoc] at h3
  exact h3

open scoped Pointwise in
theorem image_ball_scale {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (l : Measure V) [l.IsAddHaarMeasure]
    (L : E ≃L[ℝ] V) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    l (L '' Metric.ball 0 (s * r)) = ENNReal.ofReal (s ^ Module.finrank ℝ V) * l (L '' Metric.ball 0 r) := by
  have h : L '' Metric.ball 0 (s * r) = s • (L '' Metric.ball 0 r) := by
    rw [← Set.image_smul_comm L s _ (fun x => map_smul L s x), smul_ball hs.ne', smul_zero, Real.norm_of_nonneg hs.le]
  rw [h, Measure.addHaar_smul, abs_of_pos (by positivity)]

theorem eventually_image_ball_subset {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] V) {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), L '' Metric.ball 0 (s * r) ⊆ Metric.ball 0 δ := by
  have h : L ⁻¹' Metric.ball 0 δ ∈ 𝓝 (0 : E) :=
    L.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact Metric.ball_mem_nhds _ hδ)
  obtain ⟨η, hη, h⟩ := Metric.mem_nhds_iff.1 h
  filter_upwards [(densHom_tendsto_mul hs).eventually (Ioo_mem_nhdsGT hη)] with r hr
  exact Set.image_subset_iff.2 ((Metric.ball_subset_ball hr.2.le).trans h)

theorem tendsto_of_squeeze {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l ν : Measure V) [l.IsAddHaarMeasure] [IsLocallyFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c))
    (H : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ → ∀ᶠ r in 𝓝[>] (0:ℝ),
      ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r)))
    (L : E ≃L[ℝ] V) (f : ℝ → ℝ≥0∞)
    (hf : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ r in 𝓝[>] (0:ℝ),
      ν (L '' Metric.ball 0 ((1 - ε) * r)) ≤ f r ∧ f r ≤ ν (L '' Metric.ball 0 ((1 + ε) * r))) :
    Tendsto (fun r : ℝ => f r / l (L '' Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  have hl : ∀ᶠ r in 𝓝[>] (0:ℝ), l (L '' Metric.ball 0 r) ≠ 0 ∧ l (L '' Metric.ball 0 r) ≠ ⊤ := by
    filter_upwards [eventually_image_ball_subset L one_pos one_pos, self_mem_nhdsWithin] with r hr hr0
    rw [one_mul] at hr
    refine ⟨((L.toHomeomorph.isOpenMap _ Metric.isOpen_ball).measure_pos l
      ⟨L 0, 0, Metric.mem_ball_self hr0, rfl⟩).ne', ((measure_mono hr).trans_lt measure_ball_lt_top).ne⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨t, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    obtain ⟨δ, hδ, hA⟩ := lower_of_density l ν hc (fun ε h0 h1 => by
      obtain ⟨δ, hδ, h⟩ := H ε h0 h1
      exact ⟨δ, hδ, fun x hx => (h x hx).mono fun r hr => hr.2⟩) t h2
    obtain ⟨ε, e0, e1, hε⟩ := exists_eps_lt (Module.finrank ℝ V) (-1) ENNReal.coe_ne_top h1
    have hs : 0 < 1 - ε := by linarith
    filter_upwards [hl, hf ε e0 e1, eventually_image_ball_subset L hδ hs] with r hr hfr hsub
    refine hε.trans_le ((ENNReal.le_div_iff_mul_le (Or.inl hr.1) (Or.inl hr.2)).2 ?_)
    refine le_trans ?_ ((hA _ hsub).trans hfr.1)
    rw [image_ball_scale l L hs, mul_assoc, show 1 + -1 * ε = 1 - ε by ring]
  · obtain ⟨t, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    obtain ⟨δ, hδ, hA⟩ := upper_of_density l ν hc (fun ε h0 h1 => by
      obtain ⟨δ, hδ, h⟩ := H ε h0 h1
      exact ⟨δ, hδ, fun x hx => (h x hx).mono fun r hr => hr.1⟩) t h1
    obtain ⟨ε, e0, e1, hε⟩ := exists_eps_gt (Module.finrank ℝ V) 1 h2
    have hs : 0 < 1 + ε := by linarith
    filter_upwards [hl, hf ε e0 e1, eventually_image_ball_subset L hδ hs] with r hr hfr hsub
    refine lt_of_le_of_lt ((ENNReal.div_le_iff hr.1 hr.2).2 ?_) hε
    refine (hfr.2.trans (hA _ hsub)).trans ?_
    rw [image_ball_scale l L hs, mul_assoc, one_mul]

theorem tendsto_of_chart {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (l : Measure V) [l.IsAddHaarMeasure] (μ : Measure X) (e : V → X) (he : Continuous e)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hi : Set.InjOn e (Metric.ball 0 δ₀)) {c : ℝ≥0∞} (hct : c ≠ ⊤)
    (hc : Tendsto (fun r : ℝ => μ (e '' Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c))
    (H : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ → ∀ᶠ r in 𝓝[>] (0:ℝ),
      μ (e '' Metric.ball x ((1 - ε) * r)) ≤ μ (e '' Metric.ball 0 r) ∧
        μ (e '' Metric.ball 0 r) ≤ μ (e '' Metric.ball x ((1 + ε) * r)))
    (L : E ≃L[ℝ] V) (f : ℝ → ℝ≥0∞)
    (hf : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ r in 𝓝[>] (0:ℝ),
      μ (e '' (L '' Metric.ball 0 ((1 - ε) * r))) ≤ f r ∧ f r ≤ μ (e '' (L '' Metric.ball 0 ((1 + ε) * r)))) :
    Tendsto (fun r : ℝ => f r / l (L '' Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨δ, hfin, hδ, hδ'⟩ := ((hc.eventually (gt_mem_nhds hct.lt_top)).and (Ioo_mem_nhdsGT hδ₀)).exists
  have hfin' : μ (e '' Metric.ball 0 δ) < ⊤ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.top_div_of_ne_top measure_ball_lt_top.ne] at hfin
    exact lt_irrefl _ hfin
  have hψ : MeasurableEmbedding ((Metric.ball (0:V) δ).restrict e) :=
    he.continuousOn.measurableEmbedding Metric.isOpen_ball.measurableSet (hi.mono (Metric.ball_subset_ball hδ'.le))
  let ν : Measure V := (μ.comap ((Metric.ball (0:V) δ).restrict e)).map Subtype.val
  have hν : ∀ A : Set V, MeasurableSet A → ν A = μ (e '' (A ∩ Metric.ball 0 δ)) := by
    intro A hA
    simp only [ν]
    rw [Measure.map_apply measurable_subtype_coe hA, hψ.comap_apply]
    congr 1
    rw [Set.inter_comm, ← Subtype.image_preimage_coe, Set.image_image]
    rfl
  have hνb : ∀ (x : V) (r : ℝ), ‖x‖ + r ≤ δ → ν (Metric.ball x r) = μ (e '' Metric.ball x r) := by
    intro x r h
    rw [hν _ Metric.isOpen_ball.measurableSet, Set.inter_eq_left.2]
    exact Metric.ball_subset_ball' (by simpa [add_comm] using h)
  have hνL : ∀ r : ℝ, L '' Metric.ball 0 r ⊆ Metric.ball 0 δ →
      ν (L '' Metric.ball 0 r) = μ (e '' (L '' Metric.ball 0 r)) := by
    intro r h
    rw [hν (L '' Metric.ball 0 r) (L.toHomeomorph.isOpenMap _ Metric.isOpen_ball).measurableSet, Set.inter_eq_left.2 h]
  haveI : IsFiniteMeasure ν := ⟨by rw [hν _ MeasurableSet.univ, Set.univ_inter]; exact hfin'⟩
  refine tendsto_of_squeeze l ν (hc.congr' ?_) ?_ L f ?_
  · filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [hνb 0 r (by simpa using hr.2.le)]
  · intro ε h0 h1
    obtain ⟨η, hη, H⟩ := H ε h0 h1
    refine ⟨min η (δ / 2), lt_min hη (by linarith), fun x hx => ?_⟩
    have hx1 : ‖x‖ < η := hx.trans_le (min_le_left _ _)
    have hx2 : ‖x‖ < δ / 2 := hx.trans_le (min_le_right _ _)
    filter_upwards [H x hx1, Ioo_mem_nhdsGT (show (0:ℝ) < δ / 4 by linarith)] with r hr hr'
    obtain ⟨hr0, hr1⟩ := hr'
    have e1 : ε * r < r := by nlinarith
    have e2 : 0 < ε * r := by positivity
    rw [hνb x _ (by nlinarith), hνb x _ (by nlinarith), hνb 0 r (by simp; linarith)]
    exact hr
  · intro ε h0 h1
    filter_upwards [hf ε h0 h1, eventually_image_ball_subset L hδ (show 0 < 1 - ε by linarith),
      eventually_image_ball_subset L hδ (show 0 < 1 + ε by linarith)] with r hr a b
    rw [hνL _ a, hνL _ b]
    exact hr

end Meas

section Alg
variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_log (S : Set A) (J : V →L[ℝ] A) (P : A →L[ℝ] V) (hP : ∀ x, P (J x) = x)
    (hS : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ g in 𝓝 (1 : A), g ∈ S → ∃ x ∈ Metric.ball (0 : V) ρ, NormedSpace.exp (J x) = g) :
    ∃ Λ : A → V, HasStrictFDerivAt Λ P 1 ∧ (∀ᶠ x in 𝓝 (0 : V), Λ (NormedSpace.exp (J x)) = x) ∧
      ∀ᶠ g in 𝓝 (1 : A), g ∈ S → NormedSpace.exp (J (Λ g)) = g := by
  have h : HasStrictFDerivAt (NormedSpace.exp : A → A) (ContinuousLinearEquiv.refl ℝ A : A →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)
  have h1 := h.to_localInverse
  have h2 := h.eventually_left_inverse
  rw [NormedSpace.exp_zero] at h1
  have hJ : Tendsto J (𝓝 0) (𝓝 0) := by simpa using J.continuous.tendsto 0
  have h3 : ∀ᶠ x in 𝓝 (0 : V), P (h.localInverse _ _ _ (NormedSpace.exp (J x))) = x := by
    filter_upwards [hJ.eventually h2] with x hx
    rw [hx, hP]
  refine ⟨fun g => P (h.localInverse _ _ _ g), ?_, h3, ?_⟩
  · have := P.hasStrictFDerivAt.comp 1 h1
    simpa using this
  · obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff_ball.1 h3
    filter_upwards [hS ρ hρ] with g hg hgS
    obtain ⟨x, hx, rfl⟩ := hg hgS
    rw [hb x hx]

theorem hasStrict_exp (J : V →L[ℝ] A) : HasStrictFDerivAt (fun x => NormedSpace.exp (J x)) J 0 := by
  have h : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (J 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)
  exact h.comp 0 J.hasStrictFDerivAt

theorem exp_neg_mul (a : A) : NormedSpace.exp (-a) * NormedSpace.exp a = 1 := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  rw [← NormedSpace.exp_add_of_commute (Commute.refl a).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem sandwich (S : Set A) (J : V →L[ℝ] A) (P : A →L[ℝ] V) (hP : ∀ x, P (J x) = x)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hexp : ∀ x, NormedSpace.exp (J x) ∈ S)
    (Λ : A → V) (hΛ : HasStrictFDerivAt Λ P 1) (hl : ∀ᶠ x in 𝓝 (0 : V), Λ (NormedSpace.exp (J x)) = x)
    (hr : ∀ᶠ g in 𝓝 (1 : A), g ∈ S → NormedSpace.exp (J (Λ g)) = g) (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ → ∀ᶠ r in 𝓝[>] (0:ℝ),
      (∀ z ∈ Metric.ball x ((1 - ε) * r), ∃ y ∈ Metric.ball (0 : V) r,
        NormedSpace.exp (J y) = NormedSpace.exp (J (-x)) * NormedSpace.exp (J z)) ∧
      (∀ y ∈ Metric.ball (0 : V) r, ∃ z ∈ Metric.ball x ((1 + ε) * r),
        NormedSpace.exp (J z) = NormedSpace.exp (J x) * NormedSpace.exp (J y)) := by
  set e : V → A := fun x => NormedSpace.exp (J x) with he
  have e0 : e 0 = 1 := by simp [he]
  have d1 : HasStrictFDerivAt (fun p : V × V => e p.1) (J.comp (ContinuousLinearMap.fst ℝ V V)) 0 :=
    HasStrictFDerivAt.comp (g := e) (0 : V × V) (hasStrict_exp J) hasStrictFDerivAt_fst
  have d2 : HasStrictFDerivAt (fun p : V × V => e p.2) (J.comp (ContinuousLinearMap.snd ℝ V V)) 0 :=
    HasStrictFDerivAt.comp (g := e) (0 : V × V) (hasStrict_exp J) hasStrictFDerivAt_snd
  have d3 := d1.mul' d2
  have hm : (fun p : V × V => e p.1 * e p.2) 0 = 1 := by simp [e0]
  have d4 := HasStrictFDerivAt.comp (g := Λ) (f := fun p : V × V => e p.1 * e p.2) (0 : V × V)
    (hm ▸ hΛ) d3
  have d5 := d4.isLittleO.def h0
  have t : Tendsto (fun p : V × V => e p.1 * e p.2) (𝓝 0) (𝓝 1) := hm ▸ d3.continuousAt.tendsto
  obtain ⟨δ1, hδ1, k1⟩ := Metric.eventually_nhds_iff_ball.1 d5
  obtain ⟨δ2, hδ2, k2⟩ := Metric.eventually_nhds_iff_ball.1 (t.eventually hr)
  obtain ⟨δ3, hδ3, k3⟩ := Metric.eventually_nhds_iff_ball.1 hl
  have K1 : ∀ a b b' : V, ‖a‖ < δ1 → ‖b‖ < δ1 → ‖b'‖ < δ1 →
      ‖Λ (e a * e b) - Λ (e a * e b') - (b - b')‖ ≤ ε * ‖b - b'‖ := by
    intro a b b' ha hb hb'
    have := k1 ((a, b), (a, b')) (by
      simp [Prod.dist_eq, Prod.norm_def, ha, hb, hb'])
    simpa [e0, hP, Prod.norm_def] using this
  have K2 : ∀ a b : V, ‖a‖ < δ2 → ‖b‖ < δ2 → e (Λ (e a * e b)) = e a * e b := by
    intro a b ha hb
    exact k2 (a, b) (by simp [Prod.norm_def, ha, hb]) (hmul _ (hexp _) _ (hexp _))
  have L1 : Λ 1 = 0 := by rw [← e0]; exact hl.self_of_nhds
  have hδ : 0 < min δ1 (min δ2 δ3) := by positivity
  have m1 : min δ1 (min δ2 δ3) ≤ δ1 := min_le_left _ _
  have m2 : min δ1 (min δ2 δ3) ≤ δ2 := (min_le_right _ _).trans (min_le_left _ _)
  have m3 : min δ1 (min δ2 δ3) ≤ δ3 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min δ1 (min δ2 δ3) / 2, by positivity, fun x hx => ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show 0 < min δ1 (min δ2 δ3) / 2 by positivity)] with r hr
  obtain ⟨r0, r1⟩ := hr
  have er : 0 < ε * r := by positivity
  constructor
  · intro z hz
    rw [mem_ball_iff_norm] at hz
    have hz' : ‖z‖ ≤ ‖x‖ + ‖z - x‖ := norm_le_insert' z x
    have hnx : ‖-x‖ = ‖x‖ := norm_neg x
    refine ⟨Λ (e (-x) * e z), ?_, K2 _ _ (by linarith) (by linarith)⟩
    have a := K1 (-x) z x (by linarith) (by linarith) (by linarith)
    have : e (-x) * e x = 1 := by simp only [he, map_neg]; exact exp_neg_mul _
    rw [this, L1, sub_zero] at a
    have b := norm_le_insert' (Λ (e (-x) * e z)) (z - x)
    rw [mem_ball_zero_iff]
    have c : (1 + ε) * ‖z - x‖ < (1 + ε) * ((1 - ε) * r) := by gcongr
    have : 0 < ε * (ε * r) := by positivity
    nlinarith
  · intro y hy
    rw [mem_ball_zero_iff] at hy
    refine ⟨Λ (e x * e y), ?_, K2 _ _ (by linarith) (by linarith)⟩
    have a := K1 x y 0 (by linarith) (by linarith) (by simpa using hδ1)
    rw [e0, mul_one, k3 x (by rw [mem_ball_zero_iff]; linarith), sub_zero] at a
    have b := norm_le_insert' (Λ (e x * e y) - x) y
    rw [mem_ball_iff_norm]
    have c : (1 + ε) * ‖y‖ < (1 + ε) * r := by gcongr
    nlinarith

theorem norm_le_of_strict {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (ψ : E → E)
    (h : HasStrictFDerivAt ψ (ContinuousLinearMap.id ℝ E) 0) (h0 : ψ 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 (0 : E), ‖ψ x‖ ≤ (1 + ε) * ‖x‖ := by
  filter_upwards [h.hasFDerivAt.isLittleO.def hε] with x hx
  simp only [h0, sub_zero, ContinuousLinearMap.id_apply] at hx
  have := norm_le_insert' (ψ x) x
  linarith

theorem chart_squeeze {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Set A) (J : V →L[ℝ] A) (P : A →L[ℝ] V) (hP : ∀ x, P (J x) = x)
    (Λ : A → V) (hΛ : HasStrictFDerivAt Λ P 1) (hl : ∀ᶠ x in 𝓝 (0 : V), Λ (NormedSpace.exp (J x)) = x)
    (hr : ∀ᶠ g in 𝓝 (1 : A), g ∈ S → NormedSpace.exp (J (Λ g)) = g)
    (Φ : E → A) (L : E ≃L[ℝ] V) (hΦ0 : Φ 0 = 1) (hΦS : ∀ᶠ x in 𝓝 (0 : E), Φ x ∈ S)
    (hΦ : HasStrictFDerivAt Φ (J.comp (L : E →L[ℝ] V)) 0) (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    ∀ᶠ r in 𝓝[>] (0:ℝ),
      (fun x => NormedSpace.exp (J x)) '' (L '' Metric.ball 0 ((1 - ε) * r)) ⊆ Φ '' Metric.ball 0 r ∧
      Φ '' Metric.ball 0 r ⊆ (fun x => NormedSpace.exp (J x)) '' (L '' Metric.ball 0 ((1 + ε) * r)) := by
  have L1 : Λ 1 = 0 := by simpa using hl.self_of_nhds
  set ψ : E → E := fun x => L.symm (Λ (Φ x)) with hψ
  have d : HasStrictFDerivAt ψ (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 := by
    have d1 := HasStrictFDerivAt.comp (g := Λ) (f := Φ) (0 : E) (hΦ0 ▸ hΛ) hΦ
    have d2 := (L.symm : V →L[ℝ] E).hasStrictFDerivAt.comp 0 d1
    refine HasStrictFDerivAt.congr_fderiv d2 ?_
    ext x; simp [hP]
  have ψ0 : ψ 0 = 0 := by simp [hψ, hΦ0, L1]
  have di := d.to_localInverse
  have dr := d.eventually_right_inverse
  have i0 := d.localInverse_apply_image
  rw [ψ0] at di dr i0
  have t : Tendsto Φ (𝓝 0) (𝓝 1) := hΦ0 ▸ hΦ.continuousAt.tendsto
  have hE : ∀ᶠ x in 𝓝 (0 : E), NormedSpace.exp (J (L (ψ x))) = Φ x := by
    filter_upwards [t.eventually hr, hΦS] with x a b
    simpa [hψ] using a b
  obtain ⟨δ1, hδ1, k1⟩ := Metric.eventually_nhds_iff_ball.1
    (hE.and ((norm_le_of_strict ψ d ψ0 h0).and (dr.and (norm_le_of_strict _ di i0 h0))))
  filter_upwards [Ioo_mem_nhdsGT hδ1] with r hr
  obtain ⟨r0, r1⟩ := hr
  have er : 0 < ε * r := by positivity
  constructor
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [mem_ball_zero_iff] at hy
    obtain ⟨-, -, a, b⟩ := k1 y (by rw [mem_ball_zero_iff]; linarith)
    have c : (1 + ε) * ‖y‖ < (1 + ε) * ((1 - ε) * r) := by gcongr
    have : 0 < ε * (ε * r) := by positivity
    have hx : ‖d.localInverse ψ _ _ y‖ < r := by nlinarith
    refine ⟨_, mem_ball_zero_iff.2 hx, ?_⟩
    rw [← (k1 _ (by rw [mem_ball_zero_iff]; linarith)).1, a]
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_ball_zero_iff] at hx
    obtain ⟨a, b, -, -⟩ := k1 x (by rw [mem_ball_zero_iff]; linarith)
    refine ⟨_, ⟨ψ x, ?_, rfl⟩, a⟩
    rw [mem_ball_zero_iff]
    exact b.trans_lt (by gcongr)

end Alg

def lieIncl {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : lieE S →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun X := unrealify (X : EuclideanSpace ℝ _)
  map_add' X Y := by ext i j; apply Complex.ext <;> simp [unrealify]
  map_smul' a X := by ext i j; apply Complex.ext <;> simp [unrealify]

theorem lieIncl_injective {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Function.Injective (lieIncl S) := by
  intro X Y h
  ext ⟨i, j, b⟩
  have := congrFun (congrFun h i) j
  cases b
  · exact congrArg Complex.re this
  · exact congrArg Complex.im this

theorem measure_le_of_mapsTo {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hμ : PI.IsHaarOnM S μ) {s : Matrix (Fin m) (Fin m) ℂ} (hs : s ∈ S) {B C : Set (PI.MtM m)}
    (h : ∀ x ∈ B, PI.lmulQ s x ∈ C) : μ B ≤ μ C := by
  have hc : Continuous (PI.lmulQ s) :=
    Continuous.matrix_mul (A := fun _ => s) (B := fun x : PI.MtM m => Matrix.of x) continuous_const continuous_id
  calc μ B ≤ μ (PI.lmulQ s ⁻¹' C) := measure_mono h
    _ ≤ μ.map (PI.lmulQ s) C := Measure.le_map_apply hc.measurable.aemeasurable C
    _ = μ C := by rw [hμ.2.2.2 s hs]

open scoped Matrix.Norms.Operator in

theorem density_in_chart : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)) (c : ℝ≥0∞), PI.IsMatGroup S → PI.IsHaarOnM S μ → HasDens S μ c → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → Matrix (Fin m) (Fin m) ℂ) (L : E ≃L[ℝ] lieE S), Φ 0 = 1 → (∀ᶠ x in 𝓝 (0 : E), Φ x ∈ S) → (∀ i j, ∃ D : E →L[ℝ] ℂ, HasStrictFDerivAt (fun x => Φ x i j) D 0 ∧ ∀ v, D v = unrealify ((L v : lieE S) : EuclideanSpace ℝ _) i j) → Tendsto (fun ρ : ℝ => μ ((fun x => Matrix.of.symm (Φ x)) '' Metric.ball 0 ρ) / volume (L '' Metric.ball (0 : E) ρ)) (𝓝[>] 0) (𝓝 c) := by
  intro m S μ c hS hμ hc E _ _ Φ L hΦ0 hΦS hD
  obtain ⟨hlie, hnb⟩ := GlobalTheory.ClosedMatGroup.closed_subgroup m S hS
  obtain ⟨c₀, -, -, hu⟩ := GlobalTheory.T.exists_unique_haarDensity_at_identity m S μ hS hμ
  have hct : c ≠ ⊤ := by rw [hu c hc]; exact ENNReal.ofReal_ne_top
  haveI : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨P₀, hP₀⟩ := (lieIncl S).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (lieIncl_injective S))
  let J : lieE S →L[ℝ] Matrix (Fin m) (Fin m) ℂ := LinearMap.toContinuousLinearMap (lieIncl S)
  let P : Matrix (Fin m) (Fin m) ℂ →L[ℝ] lieE S := LinearMap.toContinuousLinearMap P₀
  have hP : ∀ x, P (J x) = x := fun x => LinearMap.congr_fun hP₀ x
  have hexp : ∀ x, NormedSpace.exp (J x) ∈ S := by
    intro x
    have := hlie x 1
    rw [Complex.ofReal_one, one_smul] at this
    exact this
  obtain ⟨Λ, hΛ, hl, hr⟩ := exists_log S J P hP (by
    intro ρ hρ
    obtain ⟨δ, hδ, h⟩ := hnb ρ hρ
    have : ∀ᶠ g in 𝓝 (1 : Matrix (Fin m) (Fin m) ℂ), ∀ i j, ‖(g - 1) i j‖ < δ := by
      simp only [eventually_all]
      intro i j
      have hc : Continuous fun g : Matrix (Fin m) (Fin m) ℂ => ‖(g - 1) i j‖ :=
        ((continuous_id.sub continuous_const).matrix_elem i j).norm
      exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hδ)
    filter_upwards [this] with g hg hgS
    obtain ⟨x, hx, e⟩ := h g hgS hg
    exact ⟨x, hx, e⟩)
  have hΦ : HasStrictFDerivAt Φ (J.comp (L : E →L[ℝ] lieE S)) 0 := by
    choose D hD1 hD2 using hD
    have h1 : HasStrictFDerivAt (fun x => (fun i j => Φ x i j : PI.MtM m))
        (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j => D i j) 0 :=
      hasStrictFDerivAt_pi.2 fun i => hasStrictFDerivAt_pi.2 fun j => hD1 i j
    let T : PI.MtM m →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
    have h2 := T.hasStrictFDerivAt.comp 0 h1
    refine HasStrictFDerivAt.congr_fderiv h2 ?_
    ext v i j
    exact hD2 i j v
  obtain ⟨δ₀, hδ₀, hb⟩ := Metric.eventually_nhds_iff_ball.1 hl
  letI : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have he : Continuous fun x => (Matrix.of.symm (NormedSpace.exp (J x)) : PI.MtM m) := NormedSpace.exp_continuous.comp J.continuous
  refine tendsto_of_chart (X := PI.MtM m) volume μ (fun x => Matrix.of.symm (NormedSpace.exp (J x))) he hδ₀
    ?_ hct hc ?_ L _ ?_
  · intro x hx y hy h
    have h' : NormedSpace.exp (J x) = NormedSpace.exp (J y) := h
    exact (hb x hx).symm.trans ((congrArg Λ h').trans (hb y hy))
  · intro ε h0 h1
    obtain ⟨δ, hδ, H⟩ := sandwich S J P hP hS.2.2.1 hexp Λ hΛ hl hr ε h0 h1
    refine ⟨δ, hδ, fun x hx => (H x hx).mono fun r hr => ⟨?_, ?_⟩⟩
    · refine measure_le_of_mapsTo hμ (hexp (-x)) ?_
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, e⟩ := hr.1 z hz
      exact ⟨y, hy, e⟩
    · refine measure_le_of_mapsTo hμ (hexp x) ?_
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, e⟩ := hr.2 z hz
      exact ⟨y, hy, e⟩
  · intro ε h0 h1
    filter_upwards [chart_squeeze S J P hP Λ hΛ hl hr Φ L hΦ0 hΦS hΦ ε h0 h1] with r hr
    exact ⟨measure_mono hr.1, measure_mono hr.2⟩

end GlobalTheory.ChartDensity
