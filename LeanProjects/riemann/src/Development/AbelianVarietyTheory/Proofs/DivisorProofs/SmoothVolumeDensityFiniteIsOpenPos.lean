import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.VolFin

open GlobalTheory.ChartGlue
open scoped ENNReal

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem meas_eq [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D) (c : AlgChart p σ D)
    {S : Set (CxPts p σ)} (hS : MeasurableSet S) (hc : S ⊆ c.e.source) :
    ω.meas S = ∫⁻ v in c.e '' S, ENNReal.ofReal (ω.dens c (c.e.symm v)) := by
  rw [VolDens.meas, glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [ω.trans c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hS hc,
    chartMeas_apply_of_subset _ _ hS hc]

theorem continuousOn_dens (ω : VolDens p σ D) (c : AlgChart p σ D) :
    ContinuousOn (fun v => ω.dens c (c.e.symm v)) c.e.target :=
  (ω.cont c).comp c.e.continuousOn_symm fun _ hv => c.e.map_target hv

theorem exists_open_lt_top [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ O : Set (CxPts p σ), IsOpen O ∧ y ∈ O ∧ ω.meas O < ∞ := by
  set g := fun v => ω.dens c (c.e.symm v)
  have hv0 : c.e y ∈ c.e.target := c.e.map_source hy
  have hg : ContinuousAt g (c.e y) :=
    (continuousOn_dens ω c).continuousAt (c.e.open_target.mem_nhds hv0)
  have h1 : ∀ᶠ v in 𝓝 (c.e y), g v < g (c.e y) + 1 :=
    hg.eventually (gt_mem_nhds (lt_add_one _))
  have h2 : ∀ᶠ v in 𝓝 (c.e y), v ∈ c.e.target := c.e.open_target.mem_nhds hv0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε,
    c.e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hy, Metric.mem_ball_self hε⟩, ?_⟩
  have hO : MeasurableSet (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε) :=
    (c.e.isOpen_inter_preimage Metric.isOpen_ball).measurableSet
  rw [meas_eq ω c hO Set.inter_subset_left]
  have hsub : c.e '' (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε) ⊆ Metric.ball (c.e y) ε := by
    rintro _ ⟨z, hz, rfl⟩; exact hz.2
  calc ∫⁻ v in c.e '' (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε), ENNReal.ofReal (g v)
      ≤ ∫⁻ v in Metric.ball (c.e y) ε, ENNReal.ofReal (g v) :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ ≤ ∫⁻ _ in Metric.ball (c.e y) ε, ENNReal.ofReal (g (c.e y) + 1) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
          fun v hv => ENNReal.ofReal_le_ofReal (hball v hv).1.le)
    _ = ENNReal.ofReal (g (c.e y) + 1) * volume (Metric.ball (c.e y) ε) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

theorem meas_pos [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D)
    (c : AlgChart p σ D) {U : Set (CxPts p σ)} (hU : IsOpen U) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hyU : y ∈ U) : ω.meas U ≠ 0 := by
  set g := fun v => ω.dens c (c.e.symm v)
  have hv0 : c.e y ∈ c.e.target := c.e.map_source hy
  have hg : ContinuousAt g (c.e y) :=
    (continuousOn_dens ω c).continuousAt (c.e.open_target.mem_nhds hv0)
  have hpos : 0 < g (c.e y) := by
    simp only [g, c.e.left_inv hy]; exact ω.pos c y hy
  have h1 : ∀ᶠ v in 𝓝 (c.e y), g (c.e y) / 2 < g v :=
    hg.eventually (lt_mem_nhds (half_lt_self hpos))
  have h2 : ∀ᶠ v in 𝓝 (c.e y), v ∈ c.e.target ∩ c.e.symm ⁻¹' U :=
    (isOpen_over c.e hU).mem_nhds (mem_over c.e hy hyU)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  have hA : MeasurableSet (c.e.source ∩ U) := (c.e.open_source.inter hU).measurableSet
  have hsub : Metric.ball (c.e y) ε ⊆ c.e '' (c.e.source ∩ U) := by
    rw [c.e.image_source_inter_eq']; exact fun v hv => (hball v hv).2
  refine (lt_of_lt_of_le ?_ (measure_mono (μ := ω.meas) (Set.inter_subset_right :
    c.e.source ∩ U ⊆ U))).ne'
  rw [meas_eq ω c hA Set.inter_subset_left]
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (g (c.e y) / 2) * volume (Metric.ball (c.e y) ε) :=
        ENNReal.mul_pos (ENNReal.ofReal_pos.2 (half_pos hpos)).ne' (Metric.measure_ball_pos _ _ hε).ne'
    _ = ∫⁻ _ in Metric.ball (c.e y) ε, ENNReal.ofReal (g (c.e y) / 2) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ v in Metric.ball (c.e y) ε, ENNReal.ofReal (g v) :=
        lintegral_mono_ae (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
          fun v hv => ENNReal.ofReal_le_ofReal (hball v hv).1.le)
    _ ≤ ∫⁻ v in c.e '' (c.e.source ∩ U), ENNReal.ofReal (g v) :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

end GlobalTheory.HSAmp.VolFin

open GlobalTheory.HSAmp.VolFin in

theorem GlobalTheory.HSAmp.volDens_meas_finite_openPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D),
    IsFiniteMeasure ω.meas ∧ ω.meas.IsOpenPosMeasure := by
  intro k _ X _ p D hX hS σ ω
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  haveI := hX.compactSpace σ
  obtain ⟨R⟩ := hS σ
  haveI : IsLocallyFiniteMeasure ω.meas := ⟨fun y => by
    obtain ⟨i, hi⟩ := R.cover y
    obtain ⟨O, hO, hyO, hfin⟩ := exists_open_lt_top ω (R.chart i) hi
    exact ⟨O, hO.mem_nhds hyO, hfin⟩⟩
  refine ⟨inferInstance, ⟨fun U hU ⟨y, hyU⟩ => ?_⟩⟩
  obtain ⟨i, hi⟩ := R.cover y
  exact meas_pos ω (R.chart i) hU hi hyU
