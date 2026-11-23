import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpA

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open Filter Topology Metric NormedSpace Asymptotics

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasStrictFDerivAt_exp_zero_alt : HasStrictFDerivAt (exp : 𝔸 → 𝔸)
    ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero (𝕂 := ℝ)

variable (𝔸) in

def logA : 𝔸 → 𝔸 := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse _ _ _

theorem logA_exp : ∀ᶠ X in 𝓝 (0 : 𝔸), logA 𝔸 (exp X) = X :=
  (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).eventually_left_inverse

theorem exp_logA : ∀ᶠ h in 𝓝 (1 : 𝔸), exp (logA 𝔸 h) = h := by
  have := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).eventually_right_inverse
  rwa [exp_zero] at this

theorem logA_one : logA 𝔸 (1 : 𝔸) = 0 := by
  have := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse_apply_image
  rwa [exp_zero] at this

theorem hasStrict_logA : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸) (1 : 𝔸) := by
  have := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).to_localInverse
  rw [exp_zero] at this
  exact this

theorem exp_cont : Continuous (exp : 𝔸 → 𝔸) :=
  let _ := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exp_continuous

theorem exp_neg_mul (X : 𝔸) : exp (-X) * exp X = 1 := by
  letI := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel, exp_zero]

theorem exp_mul_neg (X : 𝔸) : exp X * exp (-X) = 1 := by
  have := exp_neg_mul (-X)
  rwa [neg_neg] at this

def F1 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp (-p.1) * exp (p.1 + p.2))

def F2 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp p.1 * exp p.2)

theorem hasStrict_exp_comp (L : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => exp (L p)) L (0 : 𝔸 × 𝔸) := by
  have h1 : HasStrictFDerivAt (exp : 𝔸 → 𝔸) (ContinuousLinearMap.id ℝ 𝔸) (L 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero_alt
  exact h1.comp (0 : 𝔸 × 𝔸) L.hasStrictFDerivAt

theorem hasStrict_mul (L M : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => logA 𝔸 (exp (L p) * exp (M p))) (L + M) (0 : 𝔸 × 𝔸) := by
  have h := (hasStrict_exp_comp L).mul' (hasStrict_exp_comp M)
  have hv : ((fun p : 𝔸 × 𝔸 => exp (L p)) * fun p : 𝔸 × 𝔸 => exp (M p)) 0 = 1 := by
    simp [exp_zero]
  have h1 : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸)
      (((fun p : 𝔸 × 𝔸 => exp (L p)) * fun p : 𝔸 × 𝔸 => exp (M p)) 0) := by
    rw [hv]; exact hasStrict_logA
  refine (h1.comp (0 : 𝔸 × 𝔸) h).congr_fderiv ?_
  ext p <;> simp [exp_zero, add_comm]

theorem hasStrictFDerivAt_translateLog : HasStrictFDerivAt (F1 (𝔸 := 𝔸)) (ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := by
  have := hasStrict_mul (-(ContinuousLinearMap.fst ℝ 𝔸 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸)
  refine this.congr_fderiv ?_
  ext p <;> simp

theorem hasStrictFDerivAt_productLog : HasStrictFDerivAt (F2 (𝔸 := 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 :=
  hasStrict_mul (ContinuousLinearMap.fst ℝ 𝔸 𝔸) (ContinuousLinearMap.snd ℝ 𝔸 𝔸)

theorem eventually_pair {P : 𝔸 × 𝔸 → Prop} (h : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), P p) :
    ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ → P (X, Y) := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨δ, hδ, fun X Y hX hY => h _ ?_⟩
  rw [mem_ball_zero_iff, Prod.norm_def]
  exact max_lt hX hY

theorem strict_est {F : 𝔸 × 𝔸 → 𝔸} {F' : 𝔸 × 𝔸 →L[ℝ] 𝔸} (hF : HasStrictFDerivAt F F' 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
      ‖F (X, Y) - F (X, 0) - F' (0, Y)‖ ≤ ε * ‖Y‖ := by
  have h := hF.isLittleO.def hε
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨δ, hδ, fun X Y hX hY => ?_⟩
  have hm : (((X, Y), (X, 0)) : (𝔸 × 𝔸) × (𝔸 × 𝔸)) ∈ ball ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) δ := by
    rw [show ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) = 0 from rfl, mem_ball_zero_iff]
    simp only [Prod.norm_def, norm_zero]
    simp [hX, hY]
  have := h _ hm
  simpa [Prod.norm_def] using this

theorem distortion {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
    (exp (F1 (X, Y)) = exp (-X) * exp (X + Y) ∧ ‖F1 (X, Y) - Y‖ ≤ ε * ‖Y‖) ∧
    (exp (F2 (X, Y)) = exp X * exp Y ∧ ‖F2 (X, Y) - X - Y‖ ≤ ε * ‖Y‖) := by
  obtain ⟨δ1, h1, H1⟩ := strict_est (hasStrictFDerivAt_translateLog (𝔸 := 𝔸)) hε
  obtain ⟨δ2, h2, H2⟩ := strict_est (hasStrictFDerivAt_productLog (𝔸 := 𝔸)) hε
  have c1 : Tendsto (fun p : 𝔸 × 𝔸 => exp (-p.1) * exp (p.1 + p.2)) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun p : 𝔸 × 𝔸 => exp (-p.1) * exp (p.1 + p.2)) :=
      (exp_cont.comp continuous_fst.neg).mul (exp_cont.comp (continuous_fst.add continuous_snd))
    have h := this.tendsto 0
    simpa [exp_zero] using h
  have c2 : Tendsto (fun p : 𝔸 × 𝔸 => exp p.1 * exp p.2) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun p : 𝔸 × 𝔸 => exp p.1 * exp p.2) :=
      (exp_cont.comp continuous_fst).mul (exp_cont.comp continuous_snd)
    have h := this.tendsto 0
    simpa [exp_zero] using h
  obtain ⟨δ3, h3, H3⟩ := eventually_pair (c1.eventually exp_logA)
  obtain ⟨δ4, h4, H4⟩ := eventually_pair (c2.eventually exp_logA)
  obtain ⟨δ5, h5, H5⟩ := Metric.eventually_nhds_iff_ball.mp (logA_exp (𝔸 := 𝔸))
  refine ⟨min (min δ1 δ2) (min (min δ3 δ4) δ5), by positivity, fun X Y hX hY => ?_⟩
  simp only [lt_min_iff] at hX hY
  refine ⟨⟨H3 X Y hX.2.1.1 hY.2.1.1, ?_⟩, ⟨H4 X Y hX.2.1.2 hY.2.1.2, ?_⟩⟩
  · have := H1 X Y hX.1.1 hY.1.1
    have e : F1 (X, (0 : 𝔸)) = 0 := by simp [F1, exp_neg_mul, logA_one]
    simpa [e] using this
  · have := H2 X Y hX.1.2 hY.1.2
    have e : F2 (X, (0 : 𝔸)) = X := by
      simp only [F2, exp_zero, mul_one]
      exact H5 X (by simpa using hX.2.2)
    simpa [e] using this

end ReciprocityTheory.ChartRestriction.DS.HExp

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

structure Chart (V : Submodule ℝ 𝔸) (G : Type*) [Group G] [TopologicalSpace G] where
  mat : G →* 𝔸
  emb : IsEmbedding mat
  H1 : ∀ X : V, ∃ g, mat g = exp (X : 𝔸)
  H2 : ∀ᶠ Z in 𝓝 (0 : 𝔸), (∃ g, mat g = exp Z) → Z ∈ V

namespace Chart

variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)

def expG (X : V) : G := (C.H1 X).choose

theorem mat_expG (X : V) : C.mat (C.expG X) = exp (X : 𝔸) := (C.H1 X).choose_spec

def img (s : Set V) : Set G := {g | ∃ X ∈ s, C.mat g = exp ((X : V) : 𝔸)}

theorem img_eq (s : Set V) : C.img s = C.expG '' s := by
  ext g
  constructor
  · rintro ⟨X, hX, h⟩
    exact ⟨X, hX, C.emb.injective (by rw [mat_expG, h])⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, C.mat_expG X⟩

theorem expG_cont : Continuous C.expG := by
  rw [C.emb.isInducing.continuous_iff]
  have : C.mat ∘ C.expG = fun X : V => exp (X : 𝔸) := funext C.mat_expG
  rw [this]
  exact exp_cont.comp continuous_subtype_val

theorem exists_rho : ∃ ρ > 0, ∀ Z : 𝔸, ‖Z‖ < ρ →
    logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V) := by
  obtain ⟨ρ, hρ, h⟩ := Metric.eventually_nhds_iff_ball.mp ((logA_exp (𝔸 := 𝔸)).and C.H2)
  exact ⟨ρ, hρ, fun Z hZ => h Z (by simpa using hZ)⟩

variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))

include hR in
theorem injOn : InjOn C.expG (ball (0 : V) ρ) := by
  intro X hX Y hY h
  have hX' : ‖(X : 𝔸)‖ < ρ := by simpa using hX
  have hY' : ‖(Y : 𝔸)‖ < ρ := by simpa using hY
  have e : exp (X : 𝔸) = exp (Y : 𝔸) := by rw [← C.mat_expG, ← C.mat_expG, h]
  exact Subtype.ext (by rw [← (hR _ hX').1, e, (hR _ hY').1])

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]

include hR in
theorem meas_image {s : Set V} (hs : MeasurableSet s) (hsub : s ⊆ ball 0 ρ) :
    MeasurableSet (C.expG '' s) := by
  have : T2Space G := C.emb.t2Space
  exact hs.image_of_continuousOn_injOn C.expG_cont.continuousOn ((C.injOn hR).mono hsub)

def nu (ρ : ℝ) (μ : Measure G) : Measure V :=
  (μ.comap (fun x : ball (0 : V) ρ => C.expG x.1)).map Subtype.val

variable (μ : Measure G)

include hR in
theorem nu_apply {s : Set V} (hs : MeasurableSet s) :
    C.nu ρ μ s = μ (C.expG '' (s ∩ ball 0 ρ)) := by
  have hinj : Function.Injective (fun x : ball (0 : V) ρ => C.expG x.1) := fun x y h =>
    Subtype.ext (C.injOn hR x.2 y.2 h)
  have hm : ∀ t : Set (ball (0 : V) ρ), MeasurableSet t →
      MeasurableSet ((fun x : ball (0 : V) ρ => C.expG x.1) '' t) := by
    intro t ht
    have : (fun x : ball (0 : V) ρ => C.expG x.1) '' t = C.expG '' (Subtype.val '' t) := by
      rw [Set.image_image]
    rw [this]
    refine C.meas_image hR (MeasurableSet.subtype_image measurableSet_ball ht) ?_
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  rw [nu, Measure.map_apply measurable_subtype_coe hs,
    Measure.comap_apply _ hinj hm _ (measurable_subtype_coe hs)]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
  · rintro ⟨X, ⟨hX, hXρ⟩, rfl⟩
    exact ⟨⟨X, hXρ⟩, hX, rfl⟩

variable [IsTopologicalGroup G] [μ.IsHaarMeasure]

include hR in
theorem nu_finite : IsFiniteMeasure (C.nu ρ μ) := by
  refine ⟨?_⟩
  rw [C.nu_apply hR μ MeasurableSet.univ]
  refine lt_of_le_of_lt (measure_mono (Set.image_mono ?_))
    (((isCompact_closedBall (0 : V) ρ).image C.expG_cont).measure_lt_top (μ := μ))
  exact fun x hx => ball_subset_closedBall hx.2

include hR in
theorem nu_pos (hρ : 0 < ρ) (r : ℝ) (hr : 0 < r) : 0 < C.nu ρ μ (closedBall (0 : V) r) := by
  rw [C.nu_apply hR μ measurableSet_closedBall]
  have hc : ContinuousAt (logA 𝔸) (1 : 𝔸) := hasStrict_logA.hasFDerivAt.continuousAt
  have h1 : ∀ᶠ h in 𝓝 (1 : 𝔸), ‖logA 𝔸 h‖ < min r ρ := by
    have := hc.eventually (Metric.ball_mem_nhds (logA 𝔸 (1 : 𝔸)) (lt_min hr hρ))
    simpa [logA_one] using this
  have h2 : Tendsto C.mat (𝓝 (1 : G)) (𝓝 (1 : 𝔸)) := by
    have := C.emb.continuous.tendsto 1
    rwa [map_one] at this
  have h3 := h2.eventually (h1.and exp_logA)
  refine lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds μ h3) (measure_mono ?_)
  intro g hg
  have hg1 : ‖logA 𝔸 (C.mat g)‖ < min r ρ := hg.1
  have hg2 : exp (logA 𝔸 (C.mat g)) = C.mat g := hg.2
  have hV : logA 𝔸 (C.mat g) ∈ V := (hR _ (lt_of_lt_of_le hg1 (min_le_right _ _))).2 ⟨g, hg2.symm⟩
  refine ⟨⟨_, hV⟩, ⟨?_, ?_⟩, C.emb.injective (by rw [mat_expG]; exact hg2)⟩
  · rw [mem_closedBall_zero_iff]; exact (lt_of_lt_of_le hg1 (min_le_left _ _)).le
  · rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hg1 (min_le_right _ _)

include hR in
theorem nu_qinv (hρ : 0 < ρ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : ∃ δ > 0, QInv (C.nu ρ μ) ε δ := by
  obtain ⟨δ0, hδ0, hD⟩ := distortion (𝔸 := 𝔸) hε0
  refine ⟨min δ0 (ρ / 4), by positivity, fun X hX r hr0 hr => ?_⟩
  have hXδ : ‖(X : 𝔸)‖ < δ0 := lt_of_lt_of_le hX (min_le_left _ _)
  have hXρ : ‖(X : 𝔸)‖ < ρ / 4 := lt_of_lt_of_le hX (min_le_right _ _)
  have hrδ : r < δ0 := lt_of_lt_of_le hr (min_le_left _ _)
  have hrρ : r < ρ / 4 := lt_of_lt_of_le hr (min_le_right _ _)
  rw [C.nu_apply hR μ measurableSet_closedBall, C.nu_apply hR μ measurableSet_closedBall,
    C.nu_apply hR μ measurableSet_closedBall]
  constructor
  · rw [← measure_preimage_mul μ (C.expG X)⁻¹ (C.expG '' (closedBall 0 r ∩ ball 0 ρ))]
    refine measure_mono ?_
    rintro _ ⟨W, ⟨hW, -⟩, rfl⟩
    set Y : V := W - X with hY
    have hYn : ‖(Y : 𝔸)‖ ≤ (1 - ε) * r := by
      have := mem_closedBall_iff_norm.mp hW
      exact this
    have hYr : ‖(Y : 𝔸)‖ < δ0 := by nlinarith
    obtain ⟨⟨e1, e2⟩, -⟩ := hD X Y hXδ hYr
    have hZn : ‖F1 ((X : 𝔸), (Y : 𝔸))‖ ≤ r := by
      have h1 : ‖F1 ((X : 𝔸), (Y : 𝔸))‖ ≤ ‖F1 ((X : 𝔸), (Y : 𝔸)) - Y‖ + ‖(Y : 𝔸)‖ := by
        have := norm_add_le (F1 ((X : 𝔸), (Y : 𝔸)) - Y) (Y : 𝔸)
        simpa using this
      have h2 : (1 + ε) * ((1 - ε) * r) ≤ r := by nlinarith [mul_pos hε0 hε0]
      nlinarith [norm_nonneg (Y : 𝔸)]
    have hXY : (X : 𝔸) + (Y : 𝔸) = (W : 𝔸) := by simp [hY]
    have hZV : F1 ((X : 𝔸), (Y : 𝔸)) ∈ V := by
      refine (hR _ (by linarith)).2 ⟨C.expG (-X) * C.expG W, ?_⟩
      rw [map_mul, mat_expG, mat_expG, e1, hXY]
      simp
    refine ⟨⟨_, hZV⟩, ⟨?_, ?_⟩, C.emb.injective ?_⟩
    · rw [mem_closedBall_zero_iff]; exact hZn
    · rw [mem_ball_zero_iff]
      have : ‖F1 ((X : 𝔸), (Y : 𝔸))‖ < ρ := by linarith
      exact this
    · have hinv : C.mat (C.expG X)⁻¹ = exp (-(X : 𝔸)) := by
        have h1 : C.mat (C.expG X)⁻¹ * C.mat (C.expG X) = 1 := by rw [← map_mul]; simp
        rw [mat_expG] at h1
        calc C.mat (C.expG X)⁻¹ = C.mat (C.expG X)⁻¹ * (exp (X : 𝔸) * exp (-(X : 𝔸))) := by
              rw [exp_mul_neg, mul_one]
          _ = exp (-(X : 𝔸)) := by rw [← mul_assoc, h1, one_mul]
      rw [mat_expG, map_mul, hinv, mat_expG]
      show exp (F1 ((X : 𝔸), (Y : 𝔸))) = _
      rw [e1, hXY]
  · rw [← measure_preimage_mul μ (C.expG X) (C.expG '' (closedBall X ((1 + ε) * r) ∩ ball 0 ρ))]
    refine measure_mono ?_
    rintro _ ⟨Z, ⟨hZ, -⟩, rfl⟩
    have hZn : ‖(Z : 𝔸)‖ ≤ r := by
      have := mem_closedBall_zero_iff.mp hZ
      exact this
    obtain ⟨-, ⟨e1, e2⟩⟩ := hD X Z hXδ (lt_of_le_of_lt hZn hrδ)
    have h1 : ‖F2 ((X : 𝔸), (Z : 𝔸)) - X‖ ≤ (1 + ε) * r := by
      have := norm_add_le (F2 ((X : 𝔸), (Z : 𝔸)) - X - Z) (Z : 𝔸)
      have e : F2 ((X : 𝔸), (Z : 𝔸)) - X - Z + Z = F2 ((X : 𝔸), (Z : 𝔸)) - X := by abel
      rw [e] at this
      nlinarith [norm_nonneg (Z : 𝔸)]
    have h2 : ‖F2 ((X : 𝔸), (Z : 𝔸))‖ < ρ := by
      have := norm_add_le (F2 ((X : 𝔸), (Z : 𝔸)) - X) (X : 𝔸)
      have e : F2 ((X : 𝔸), (Z : 𝔸)) - X + X = F2 ((X : 𝔸), (Z : 𝔸)) := by abel
      rw [e] at this
      nlinarith
    have hV : F2 ((X : 𝔸), (Z : 𝔸)) ∈ V := by
      refine (hR _ h2).2 ⟨C.expG X * C.expG Z, ?_⟩
      rw [map_mul, mat_expG, mat_expG, e1]
    refine ⟨⟨_, hV⟩, ⟨?_, ?_⟩, C.emb.injective ?_⟩
    · rw [mem_closedBall_iff_norm]; exact h1
    · rw [mem_ball_zero_iff]; exact h2
    · rw [mat_expG, map_mul, mat_expG, mat_expG]
      exact e1

theorem exists_density (lam : Measure V) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ (C.img (S r)) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨ρ, hρ, hR⟩ := C.exists_rho
  have := C.nu_finite hR μ
  obtain ⟨c, hc0, hct, hup, hdown⟩ := HExp.exists_density lam (C.nu ρ μ)
    (fun ε h0 h1 => C.nu_qinv hR μ hρ ε h0 h1) (fun r hr => C.nu_pos hR μ hρ r hr)
  refine ⟨c, hc0, hct, fun S hSm hS hS0 => ?_⟩
  refine (tendsto_ratio lam (C.nu ρ μ) hup hdown S hS hS0).congr' ?_
  filter_upwards [hS ρ hρ] with r hr
  rw [C.nu_apply hR μ (hSm r), Set.inter_eq_self_of_subset_left hr, img_eq]

theorem exists_density_unif (lam : Measure V) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ D : ℝ≥0, c < D → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        μ (C.img s) ≤ D * lam s) ∧
      (∀ D : ℝ≥0, (D : ℝ≥0∞) < c → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        D * lam s ≤ μ (C.img s)) := by
  obtain ⟨ρ, hρ, hR⟩ := C.exists_rho
  have := C.nu_finite hR μ
  obtain ⟨c, hc0, hct, hup, hdown⟩ := HExp.exists_density lam (C.nu ρ μ)
    (fun ε h0 h1 => C.nu_qinv hR μ hρ ε h0 h1) (fun r hr => C.nu_pos hR μ hρ r hr)
  have key : ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) ρ → C.nu ρ μ s = μ (C.img s) := by
    intro s hs hsρ
    rw [C.nu_apply hR μ hs, Set.inter_eq_self_of_subset_left hsρ, img_eq]
  refine ⟨c, hc0, hct, fun D hD => ?_, fun D hD => ?_⟩
  · obtain ⟨δ, hδ, h⟩ := hup D hD
    refine ⟨min δ ρ, lt_min hδ hρ, fun s hsm hs => ?_⟩
    rw [← key s hsm (hs.trans (ball_subset_ball (min_le_right _ _)))]
    exact h s (hs.trans (ball_subset_ball (min_le_left _ _)))
  · obtain ⟨δ, hδ, h⟩ := hdown D hD
    refine ⟨min δ ρ, lt_min hδ hρ, fun s hsm hs => ?_⟩
    rw [← key s hsm (hs.trans (ball_subset_ball (min_le_right _ _)))]
    exact h s (hs.trans (ball_subset_ball (min_le_left _ _)))

end Chart

theorem Chart.exists_density' {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ X ∈ S r, ‖(X : 𝔸)‖ < δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ {g | ∃ X ∈ S r, C.mat g = exp ((X : V) : 𝔸)} / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨c, h0, ht, h⟩ := C.exists_density μ lam
  refine ⟨c, h0, ht, fun S hm hS hS0 => h S hm (fun δ hδ => ?_) hS0⟩
  filter_upwards [hS δ hδ] with r hr X hX
  rw [mem_ball_zero_iff]
  exact hr X hX

theorem Chart.exists_density_unif' {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ D : ℝ≥0, c < D → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        μ (C.img s) ≤ D * lam s) ∧
      (∀ D : ℝ≥0, (D : ℝ≥0∞) < c → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        D * lam s ≤ μ (C.img s)) :=
  C.exists_density_unif μ lam

end ReciprocityTheory.ChartRestriction.DS.HExp
