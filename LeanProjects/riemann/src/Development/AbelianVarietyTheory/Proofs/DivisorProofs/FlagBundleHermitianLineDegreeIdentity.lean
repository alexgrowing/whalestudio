import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCurvatureAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensityBoundNearPointStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineCos

theorem map_cosSq_part_le : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ,
      ∃ C : ENNReal, C ≠ ⊤ ∧ Measure.map v ((hY.atlas σ).part α ε) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv α hα ε
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have loc : ∀ y : CxPts p σ, ∃ W : Set (CxPts p σ), IsOpen W ∧ y ∈ W ∧ ContinuousOn v W ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map v (((hY.atlas σ).part α ε).restrict W) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
    intro y
    obtain ⟨c, G, s, O, hy, hO, hcy, hOt, hG, hGp⟩ := GlobalTheory.T.flag_bundle_curvature_at_point k B Y q p d hB hY π w E h H flB fl hfl σ v hv y
    have hρ : ContinuousOn (fun z => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α c z) O :=
      (continuousOn_const.mul ((hY.atlas σ).continuousOn_reDens hα c)).mono hOt
    obtain ⟨N, hN, hzN, hNO, C, hC, hle⟩ :=
      GlobalTheory.T.local_density_bound_near_point d O (fun z => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α c z) G s (c.e y) hO hcy hρ hG fun z hz => (hGp z hz).1
    have hWo : IsOpen (c.e.source ∩ c.e ⁻¹' N) := c.e.isOpen_inter_preimage hN
    have hWc : ContinuousOn v (c.e.source ∩ c.e ⁻¹' N) := by
      have hF := GlobalTheory.LineCos.continuousOn_cosSq s hG fun z hz => (hGp z hz).1
      have : ContinuousOn (fun y => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base (c.e y))) (GlobalTheory.LineCos.fib (c.e y)))
          (c.e.source ∩ c.e ⁻¹' N) :=
        hF.comp (c.e.continuousOn.mono Set.inter_subset_left) fun y hy => hNO hy.2
      refine this.congr fun y' hy' => ?_
      have := (hGp (c.e y') (hNO hy'.2)).2
      rwa [c.e.left_inv hy'.1] at this
    refine ⟨_, hWo, ⟨hy, hzN⟩, hWc, C, hC, ?_⟩
    set W := c.e.source ∩ c.e ⁻¹' N with hWdef
    have hWm : MeasurableSet W := hWo.measurableSet
    have hNt : N ⊆ c.e.target := hNO.trans hOt
    set ν := (volume.restrict N).withDensity fun z => ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α c z) with hνdef
    have haem : AEMeasurable c.e.symm ν :=
      ((c.e.continuousOn_symm.mono hNt).aemeasurable hN.measurableSet).mono_ac (withDensity_absolutelyContinuous _ _)
    have hcompat : ∀ (i j : (hY.atlas σ).ι) (y : CxPts p σ), y ∈ ((hY.atlas σ).e i).source → y ∈ ((hY.atlas σ).e j).source →
        ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α i ((hY.atlas σ).e i y)) =
          ENNReal.ofReal (‖ChartGlue.transDet ((hY.atlas σ).e i) ((hY.atlas σ).e j) y‖ ^ 2) *
            ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α j ((hY.atlas σ).e j y)) :=
      (hY.atlas σ).ofReal_compat (fun i v => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α i v)
        (fun i j y hi hj => by rw [(hY.atlas σ).reDens_compat hα i j y hi hj]; ring)
    have hrest : ((hY.atlas σ).part α ε).restrict W = Measure.map c.e.symm ν := by
      ext A hA
      have hAW : MeasurableSet (A ∩ W) := hA.inter hWm
      have hsub : A ∩ W ⊆ c.e.source := fun y hy => hy.2.1
      have hp : (hY.atlas σ).part α ε = ChartGlue.glueMeas (hY.atlas σ).e
          (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α i ((hY.atlas σ).e i y))) := rfl
      rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable haem hA, hp,
        ChartGlue.glueMeas_apply _ _ (hY.atlas σ).holo hcompat c hAW hsub,
        ChartGlue.chartMeas_apply_of_subset ((hY.atlas σ).e c) _ hAW hsub, hνdef, withDensity_apply' _ _,
        Measure.restrict_restrict' hN.measurableSet]
      have himg : (c.e '' (A ∩ W)) = c.e.symm ⁻¹' A ∩ N := by
        ext z
        constructor
        · rintro ⟨y', ⟨hyA, hys, hyN⟩, rfl⟩
          exact ⟨by simpa [c.e.left_inv hys] using hyA, hyN⟩
        · rintro ⟨hzA, hzN'⟩
          exact ⟨c.e.symm z, ⟨hzA, c.e.map_target (hNt hzN'), by simpa [c.e.right_inv (hNt hzN')] using hzN'⟩,
            c.e.right_inv (hNt hzN')⟩
      change ∫⁻ v in c.e '' (A ∩ W), ENNReal.ofReal (((ε : ℤ) : ℝ) *
          (hY.atlas σ).reDens α c (c.e (c.e.symm v))) = _
      rw [himg]
      refine setLIntegral_congr_fun (himg ▸ ChartGlue.measurableSet_image _ hAW hsub) fun z hz => ?_
      rw [c.e.right_inv (hNt hz.2)]
    have hvae : AEMeasurable v (Measure.map c.e.symm ν) := by
      rw [← hrest]
      exact hWc.aemeasurable hWm
    rw [hrest, AEMeasurable.map_map_of_aemeasurable hvae haem]
    refine le_of_eq_of_le (Measure.map_congr ?_) hle
    refine (withDensity_absolutelyContinuous _ _).ae_le ((ae_restrict_iff' hN.measurableSet).2
      (Filter.Eventually.of_forall fun z hz => (hGp z (hNO hz)).2))

  choose W hWo hyW hWc C hC hle using loc
  have hvc : Continuous v :=
    continuous_iff_continuousAt.2 fun y => (hWc y).continuousAt ((hWo y).mem_nhds (hyW y))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩
  refine ⟨∑ y ∈ t, C y, ENNReal.sum_ne_top.2 fun y _ => hC y, Measure.le_iff.2 fun S hS => ?_⟩
  have hsub : v ⁻¹' S ⊆ ⋃ y ∈ t, (v ⁻¹' S ∩ W y) := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Set.mem_iUnion₂.2 ⟨y, hy, hx, hxy⟩
  calc Measure.map v ((hY.atlas σ).part α ε) S = (hY.atlas σ).part α ε (v ⁻¹' S) :=
        Measure.map_apply hvc.measurable hS
    _ ≤ ∑ y ∈ t, (hY.atlas σ).part α ε (v ⁻¹' S ∩ W y) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le t _)
    _ = ∑ y ∈ t, Measure.map v (((hY.atlas σ).part α ε).restrict (W y)) S := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Measure.map_apply hvc.measurable hS, Measure.restrict_apply (hvc.measurable hS)]
    _ ≤ ∑ y ∈ t, C y * volume.restrict (Set.Icc (0 : ℝ) 1) S :=
        Finset.sum_le_sum fun y _ => Measure.le_iff.1 (hle y) S hS
    _ = ((∑ y ∈ t, C y) • volume.restrict (Set.Icc (0 : ℝ) 1)) S := by
        rw [Measure.smul_apply, smul_eq_mul, Finset.sum_mul]

end GlobalTheory.LineCos
