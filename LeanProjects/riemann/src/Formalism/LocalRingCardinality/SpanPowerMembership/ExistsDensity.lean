import Formalism.LocalRingCardinality.SpanPowerMembership.LeOfEventuallyDown
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero

noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

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
  · rintro ⟨X, hX, hg⟩
    refine ⟨X, hX, C.emb.injective ?_⟩
    rw [C.mat_expG, hg]
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, C.mat_expG X⟩

theorem expG_cont : Continuous C.expG := by
  rw [C.emb.continuous_iff]
  have h : C.mat ∘ C.expG = fun X : V => exp (X : 𝔸) := funext C.mat_expG
  rw [h]
  have hc : Continuous (fun Z : 𝔸 => exp Z) := by
    first
      | exact NormedSpace.exp_continuous (𝕂 := ℝ)
      | exact (NormedSpace.exp_continuous (𝕂 := ℝ) (𝔸 := 𝔸))
      | exact continuous_iff_continuousAt.2 fun Z => (NormedSpace.exp_analytic (𝕂 := ℝ) Z).continuousAt
      | exact NormedSpace.exp_continuous
  exact hc.comp continuous_subtype_val

theorem exists_rho : ∃ ρ > 0, ∀ Z : 𝔸, ‖Z‖ < ρ →
    logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V) := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 ((logA_exp (𝔸 := 𝔸)).and C.H2)
  exact ⟨ε, hε, fun Z hZ => h (by simpa [dist_zero_right] using hZ)⟩

variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))

include hR in
theorem injOn : InjOn C.expG (ball (0 : V) ρ) := by
  intro X hX Y hY hXY
  have h1 : exp (X : 𝔸) = exp (Y : 𝔸) := by
    rw [← C.mat_expG, ← C.mat_expG, hXY]
  have hXn : ‖(X : 𝔸)‖ < ρ := by simpa using hX
  have hYn : ‖(Y : 𝔸)‖ < ρ := by simpa using hY
  apply Subtype.ext
  rw [← (hR _ hXn).1, ← (hR _ hYn).1, h1]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]

include hR in
theorem meas_image {s : Set V} (hs : MeasurableSet s) (hsub : s ⊆ ball 0 ρ) :
    MeasurableSet (C.expG '' s) := by
  haveI : T2Space G := C.emb.t2Space
  haveI : CompleteSpace V := FiniteDimensional.complete ℝ V
  exact hs.image_of_continuousOn_injOn C.expG_cont.continuousOn ((C.injOn hR).mono hsub)

def nu (ρ : ℝ) (μ : Measure G) : Measure V :=
  (μ.comap (fun x : ball (0 : V) ρ => C.expG x.1)).map Subtype.val

variable (μ : Measure G)

include hR in
theorem nu_apply {s : Set V} (hs : MeasurableSet s) :
    C.nu ρ μ s = μ (C.expG '' (s ∩ ball 0 ρ)) := by
  unfold nu
  rw [Measure.map_apply measurable_subtype_coe hs]
  have hf : Function.Injective (fun x : ball (0 : V) ρ => C.expG x.1) :=
    fun a b h => Subtype.ext (C.injOn hR a.2 b.2 h)
  have hfm : ∀ t : Set (ball (0 : V) ρ), MeasurableSet t →
      MeasurableSet ((fun x : ball (0 : V) ρ => C.expG x.1) '' t) := by
    intro t ht
    have h1 : (fun x : ball (0 : V) ρ => C.expG x.1) '' t = C.expG '' (Subtype.val '' t) := by
      rw [Set.image_image]
    rw [h1]
    exact C.meas_image hR (MeasurableSet.subtype_image measurableSet_ball ht)
      (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  rw [Measure.comap_apply _ hf hfm μ (measurable_subtype_coe hs)]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
  · rintro ⟨X, ⟨hXs, hXb⟩, rfl⟩
    exact ⟨⟨X, hXb⟩, hXs, rfl⟩

variable [IsTopologicalGroup G] [μ.IsHaarMeasure]

include hR in
theorem nu_finite : IsFiniteMeasure (C.nu ρ μ) := by
  constructor
  rw [C.nu_apply hR μ MeasurableSet.univ, Set.univ_inter]
  have hK : IsCompact (C.expG '' closedBall (0 : V) ρ) := (isCompact_closedBall 0 ρ).image C.expG_cont
  exact lt_of_le_of_lt (measure_mono (Set.image_mono ball_subset_closedBall)) hK.measure_lt_top

include hR in
theorem nu_pos (hρ : 0 < ρ) (r : ℝ) (hr : 0 < r) : 0 < C.nu ρ μ (closedBall (0 : V) r) := by
  have ht : 0 < min r ρ := lt_min hr hρ
  have hcont : ContinuousAt (logA 𝔸) 1 := (hasStrict_logA (𝔸 := 𝔸)).hasFDerivAt.continuousAt
  have hlim : Tendsto (logA 𝔸) (𝓝 1) (𝓝 0) := by
    have h := hcont.tendsto
    rwa [logA_one] at h
  have hev : ∀ᶠ h in 𝓝 (1 : 𝔸), exp (logA 𝔸 h) = h ∧ ‖logA 𝔸 h‖ < min r ρ := by
    refine (exp_logA (𝔸 := 𝔸)).and ?_
    filter_upwards [(Metric.tendsto_nhds.1 hlim) _ ht] with h hh
    simpa [dist_zero_right] using hh
  obtain ⟨W, hWsub, hWo, hW1⟩ := _root_.mem_nhds_iff.1 hev
  have hUo : IsOpen (C.mat ⁻¹' W) := hWo.preimage C.emb.continuous
  have hU1 : (1 : G) ∈ C.mat ⁻¹' W := by
    show C.mat 1 ∈ W
    rw [map_one]
    exact hW1
  have hsub : C.mat ⁻¹' W ⊆ C.expG '' (closedBall 0 r ∩ ball 0 ρ) := by
    intro g hg
    obtain ⟨he, hn⟩ := hWsub hg
    have hZρ : ‖logA 𝔸 (C.mat g)‖ < ρ := lt_of_lt_of_le hn (min_le_right _ _)
    have hZV : logA 𝔸 (C.mat g) ∈ V := (hR _ hZρ).2 ⟨g, he.symm⟩
    refine ⟨⟨logA 𝔸 (C.mat g), hZV⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact le_of_lt (lt_of_lt_of_le hn (min_le_left _ _))
    · rw [mem_ball_zero_iff]
      exact hZρ
    · apply C.emb.injective
      rw [C.mat_expG]
      exact he
  rw [C.nu_apply hR μ measurableSet_closedBall]
  exact lt_of_lt_of_le (hUo.measure_pos μ ⟨1, hU1⟩) (measure_mono hsub)

include hR in
theorem nu_qinv (hρ : 0 < ρ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : ∃ δ > 0, QInv (C.nu ρ μ) ε δ := by
  obtain ⟨κ, hκ, hd⟩ := distortion (𝔸 := 𝔸) (half_pos hε0)
  refine ⟨min κ ρ / 3, by positivity, ?_⟩
  intro X hX r hr0 hrδ
  have hm1 : min κ ρ ≤ κ := min_le_left _ _
  have hm2 : min κ ρ ≤ ρ := min_le_right _ _
  have hXn : ‖(X : 𝔸)‖ < min κ ρ / 3 := hX
  have hX0 : 0 ≤ ‖(X : 𝔸)‖ := norm_nonneg _
  have hmul : ∀ a b : G, C.mat (a * b) = C.mat a * C.mat b := fun a b => map_mul _ _ _
  constructor
  · rw [C.nu_apply hR μ measurableSet_closedBall, C.nu_apply hR μ measurableSet_closedBall,
      ← measure_smul μ (C.expG (-X))]
    apply measure_mono
    rintro _ ⟨_, ⟨Y, ⟨hY1, hY2⟩, rfl⟩, rfl⟩
    have hW : ‖(Y : 𝔸) - X‖ ≤ (1 - ε) * r := by
      rw [mem_closedBall_iff_norm] at hY1
      exact hY1
    have hW0 : 0 ≤ ‖(Y : 𝔸) - X‖ := norm_nonneg _
    have hWk : ‖(Y : 𝔸) - X‖ < κ := by nlinarith
    obtain ⟨⟨he, hn⟩, -⟩ := hd X ((Y : 𝔸) - X) (by linarith) hWk
    have hXY : (X : 𝔸) + ((Y : 𝔸) - X) = Y := by abel
    rw [hXY] at he
    have h1 := norm_sub_norm_le (F1 ((X : 𝔸), (Y : 𝔸) - X)) ((Y : 𝔸) - X)
    have hp : (1 + ε / 2) * ‖(Y : 𝔸) - X‖ ≤ (1 + ε / 2) * ((1 - ε) * r) :=
      mul_le_mul_of_nonneg_left hW (by linarith)
    have hq : (1 + ε / 2) * ((1 - ε) * r) ≤ r := by
      nlinarith [mul_pos hε0 hr0, mul_pos (mul_pos hε0 hε0) hr0]
    have hZn : ‖F1 ((X : 𝔸), (Y : 𝔸) - X)‖ ≤ r := by linarith
    have hZρ : ‖F1 ((X : 𝔸), (Y : 𝔸) - X)‖ < ρ := by linarith
    have hex : exp (F1 ((X : 𝔸), (Y : 𝔸) - X)) = C.mat (C.expG (-X) * C.expG Y) := by
      rw [hmul, C.mat_expG, C.mat_expG, he, Submodule.coe_neg]
    have hZV := (hR _ hZρ).2 ⟨_, hex.symm⟩
    refine ⟨⟨_, hZV⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact hZn
    · rw [mem_ball_zero_iff]
      exact hZρ
    · apply C.emb.injective
      rw [C.mat_expG]
      exact hex
  · rw [C.nu_apply hR μ measurableSet_closedBall, C.nu_apply hR μ measurableSet_closedBall,
      ← measure_smul μ (C.expG X)]
    apply measure_mono
    rintro _ ⟨_, ⟨Z, ⟨hZ1, hZ2⟩, rfl⟩, rfl⟩
    have hZ : ‖(Z : 𝔸)‖ ≤ r := by
      rw [mem_closedBall_zero_iff] at hZ1
      exact hZ1
    have hZ0 : 0 ≤ ‖(Z : 𝔸)‖ := norm_nonneg _
    obtain ⟨-, ⟨he, hn⟩⟩ := hd X Z (by linarith) (by linarith)
    have h1 := norm_sub_norm_le (F2 ((X : 𝔸), (Z : 𝔸)) - X) (Z : 𝔸)
    have hp : ε / 2 * ‖(Z : 𝔸)‖ ≤ ε / 2 * r := mul_le_mul_of_nonneg_left hZ (by linarith)
    have hq : ε * r ≤ r := by nlinarith [mul_pos hε0 hr0]
    have hYX : ‖F2 ((X : 𝔸), (Z : 𝔸)) - X‖ ≤ (1 + ε) * r := by
      calc ‖F2 ((X : 𝔸), (Z : 𝔸)) - X‖ ≤ ‖F2 ((X : 𝔸), (Z : 𝔸)) - X - Z‖ + ‖(Z : 𝔸)‖ := by linarith [h1]
        _ ≤ ε / 2 * ‖(Z : 𝔸)‖ + r := add_le_add hn hZ
        _ ≤ ε / 2 * r + r := by linarith [hp]
        _ ≤ (1 + ε) * r := by nlinarith [mul_pos hε0 hr0]
    have h2 := norm_le_insert' (F2 ((X : 𝔸), (Z : 𝔸))) (X : 𝔸)
    have hYρ : ‖F2 ((X : 𝔸), (Z : 𝔸))‖ < ρ := by linarith
    have hex : exp (F2 ((X : 𝔸), (Z : 𝔸))) = C.mat (C.expG X * C.expG Z) := by
      rw [hmul, C.mat_expG, C.mat_expG, he]
    have hYV := (hR _ hYρ).2 ⟨_, hex.symm⟩
    refine ⟨⟨_, hYV⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_iff_norm]
      exact hYX
    · rw [mem_ball_zero_iff]
      exact hYρ
    · apply C.emb.injective
      rw [C.mat_expG]
      exact hex

theorem exists_density (lam : Measure V) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ (C.img (S r)) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨ρ, hρ, hR⟩ := C.exists_rho
  haveI := C.nu_finite hR μ
  obtain ⟨c, hc0, hctop, hup, hdown⟩ := Formalism.BasicNotions.Examples₂.CD.exists_density (nu := C.nu ρ μ) (lam := lam)
    (fun ε h0 h1 => C.nu_qinv hR μ hρ ε h0 h1) (fun r hr => C.nu_pos hR μ hρ r hr)
  refine ⟨c, hc0, hctop, fun S hS hsmall hlam => ?_⟩
  have key : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      S r ⊆ ball 0 δ ∧ S r ⊆ ball 0 ρ ∧ lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤ := fun δ hδ =>
    (((hsmall δ hδ).and (hsmall ρ hρ)).and hlam).mono fun r h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have heq : ∀ r, S r ⊆ ball 0 ρ → μ (C.img (S r)) = C.nu ρ μ (S r) := by
    intro r hr
    rw [C.img_eq, C.nu_apply hR μ (hS r), Set.inter_eq_left.2 hr]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨C', haC', hC'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    obtain ⟨δ, hδ, hδs⟩ := hdown C' hC'c
    filter_upwards [key δ hδ] with r hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [heq r h2]
    exact lt_of_lt_of_le haC' ((ENNReal.le_div_iff_mul_le (Or.inl h3) (Or.inl h4)).2 (hδs _ h1))
  · obtain ⟨C', hcC', hC'b⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb
    obtain ⟨δ, hδ, hδs⟩ := hup C' hcC'
    filter_upwards [key δ hδ] with r hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [heq r h2]
    exact lt_of_le_of_lt (ENNReal.div_le_of_le_mul (hδs _ h1)) hC'b

end Chart

theorem Chart.exists_density' {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ X ∈ S r, ‖(X : 𝔸)‖ < δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ {g | ∃ X ∈ S r, C.mat g = exp ((X : V) : 𝔸)} / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  letI := mV
  letI := mG
  haveI := _hfd
  haveI := _hbV
  haveI := _hbG
  haveI := _hG
  haveI := _hμ
  haveI := _hlam
  obtain ⟨c, h0, h1, h⟩ := C.exists_density μ lam
  refine ⟨c, h0, h1, fun S hS hsm hl => h S hS (fun δ hδ => (hsm δ hδ).mono fun r hr X hX => ?_) hl⟩
  simpa using hr X hX

end Formalism.BasicNotions.Examples₂.CD
