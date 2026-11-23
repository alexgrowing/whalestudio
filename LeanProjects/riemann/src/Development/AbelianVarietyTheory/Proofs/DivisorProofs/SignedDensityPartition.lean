import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchLim.DomConv

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem part_compl_iUnion_source (ρ : AlgChart p σ D → CxPts p σ → ℝ) :
    part ρ (⋃ c : AlgChart p σ D, c.e.source)ᶜ = 0 := by
  set U := ⋃ c : AlgChart p σ D, c.e.source with hUdef
  have hU : MeasurableSet U := (isOpen_iUnion fun c => c.e.open_source).measurableSet
  have hle : part ρ ≤ (part ρ).restrict U := by
    show (⨆ c : AlgChart p σ D, ChartGlue.chartMeas c.e fun y => ENNReal.ofReal (ρ c y)) ≤ _
    refine iSup_le fun c => Measure.le_iff.2 fun A hA => ?_
    rw [Measure.restrict_apply hA]
    calc ChartGlue.chartMeas c.e (fun y => ENNReal.ofReal (ρ c y)) A
        = ChartGlue.chartMeas c.e (fun y => ENNReal.ofReal (ρ c y)) (c.e.source ∩ A) := by
          rw [ChartGlue.chartMeas_apply _ _ hA, ChartGlue.chartMeas_apply_of_subset _ _
            (c.e.open_source.measurableSet.inter hA) Set.inter_subset_left]
      _ ≤ part ρ (c.e.source ∩ A) :=
          Measure.le_iff'.1 (le_iSup (fun c : AlgChart p σ D =>
            ChartGlue.chartMeas c.e fun y => ENNReal.ofReal (ρ c y)) c) _
      _ ≤ part ρ (A ∩ U) := measure_mono fun y hy => ⟨hy.2, Set.mem_iUnion.2 ⟨c, hy.1⟩⟩
  refine le_antisymm ?_ bot_le
  calc part ρ Uᶜ ≤ (part ρ).restrict U Uᶜ := Measure.le_iff'.1 hle _
    _ = 0 := by rw [Measure.restrict_apply' hU, Set.compl_inter_self, measure_empty]

theorem isMDens_neg {ρ : AlgChart p σ D → CxPts p σ → ℝ} (h : IsMDens ρ) : IsMDens fun c y => -ρ c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy']; ring, fun c => (h.2 c).neg⟩

theorem setLIntegral_part_chart [SecondCountableTopology (CxPts p σ)] {w : AlgChart p σ D → CxPts p σ → ℝ}
    (h : IsMDens w) (c : AlgChart p σ D) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (hc : A ⊆ c.e.source)
    {f : CxPts p σ → ℝ≥0∞} (hf : AEMeasurable f ((part w).restrict A)) :
    ∫⁻ y in A, f y ∂(part w) =
      ∫⁻ v in c.e '' A, ENNReal.ofReal (w c (c.e.symm v)) * f (c.e.symm v) := by
  have hS := ChartGlue.measurableSet_image c.e hA hc
  have hSt : c.e '' A ⊆ c.e.target := (Set.image_mono hc).trans c.e.image_source_eq_target.subset
  have hsym : AEMeasurable c.e.symm (volume.restrict (c.e '' A)) :=
    (c.e.continuousOn_symm.mono hSt).aemeasurable hS
  have hφ : AEMeasurable (fun v => ENNReal.ofReal (w c (c.e.symm v))) (volume.restrict (c.e '' A)) :=
    ((h.2 c).mono_measure (Measure.restrict_mono hSt le_rfl)).ennreal_ofReal
  have hsym' := hsym.mono_ac (withDensity_absolutelyContinuous (volume.restrict (c.e '' A))
    fun v => ENNReal.ofReal (w c (c.e.symm v)))
  have hpa : ∀ {T : Set (CxPts p σ)}, MeasurableSet T → T ⊆ c.e.source →
      part w T = ∫⁻ v in c.e '' T, ENNReal.ofReal (w c (c.e.symm v)) := fun hT hTc => by
    rw [GlobalTheory.MixDens.part, ChartGlue.glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
      rw [h.1 c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hT hTc,
      ChartGlue.chartMeas_apply_of_subset _ _ hT hTc]
  have key : (part w).restrict A = Measure.map c.e.symm
      ((volume.restrict (c.e '' A)).withDensity fun v => ENNReal.ofReal (w c (c.e.symm v))) := by
    ext B hB
    rw [Measure.restrict_apply hB, hpa (hB.inter hA) (Set.inter_subset_right.trans hc),
      Measure.map_apply_of_aemeasurable hsym' hB, withDensity_apply',
      Measure.restrict_restrict' hS]
    congr 2
    ext v
    constructor
    · rintro ⟨y, ⟨hyB, hyA⟩, rfl⟩
      exact ⟨by rwa [Set.mem_preimage, c.e.left_inv (hc hyA)], ⟨y, hyA, rfl⟩⟩
    · rintro ⟨hv, ⟨y, hyA, rfl⟩⟩
      rw [Set.mem_preimage, c.e.left_inv (hc hyA)] at hv
      exact ⟨y, ⟨hv, hyA⟩, rfl⟩
  rw [key] at hf
  rw [key, lintegral_map' hf hsym']
  exact lintegral_withDensity_eq_lintegral_mul₀' hφ (hf.comp_aemeasurable hsym')

theorem ofReal_mul_add_ofReal_neg_mul (a b : ℝ) :
    ENNReal.ofReal a * ENNReal.ofReal ‖b‖ + ENNReal.ofReal (-a) * ENNReal.ofReal ‖b‖ = ENNReal.ofReal |b * a| := by
  rw [Real.norm_eq_abs]
  rcases le_total 0 a with ha | ha
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 ha), zero_mul, add_zero, ← ENNReal.ofReal_mul ha, abs_mul,
      abs_of_nonneg ha, mul_comm]
  · rw [ENNReal.ofReal_of_nonpos ha, zero_mul, zero_add, ← ENNReal.ofReal_mul (neg_nonneg.2 ha), abs_mul,
      abs_of_nonpos ha, mul_comm]

end GlobalTheory.ArchLim.DomConv

namespace GlobalTheory.ArchLim

open GlobalTheory.ArchLim.DomConv in

theorem tendsto_densInt_of_dominated : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [SecondCountableTopology (CxPts p σ)] (ρ : ℝ → AlgChart p σ D → CxPts p σ → ℝ) (f : ℝ → CxPts p σ → ℝ) (w : AlgChart p σ D → CxPts p σ → ℝ) (F : CxPts p σ → ℝ) (S : Set (CxPts p σ)), (∀ R, IsDens (ρ R)) → (∀ R, Measurable (f R)) → IsMDens w → Integrable F (part w) → MeasurableSet S → (∀ R, part (ρ R) Sᶜ = 0 ∧ part (fun c y => -ρ R c y) Sᶜ = 0) → (∀ y, 0 ≤ F y) → (∀ᶠ R in atTop, ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, y ∈ S → |f R y * ρ R c y| ≤ F y * w c y) → (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, y ∈ S → Tendsto (fun R => f R y * ρ R c y) atTop (𝓝 0)) → Tendsto (fun R => densInt (ρ R) (f R)) atTop (𝓝 0) := by
  intro k _ X p σ D _ ρ f w F S hρ hf hw hF hS hSρ hF0 hdom hlim
  by_cases hne : Nonempty (AlgChart p σ D)
  swap
  · haveI := not_nonempty_iff.1 hne
    have h0 : ∀ τ : AlgChart p σ D → CxPts p σ → ℝ, part τ = 0 := fun τ =>
      Measure.measure_univ_eq_zero.1 (by simpa using part_compl_iUnion_source τ)
    refine tendsto_const_nhds.congr fun R => ?_
    simp [densInt, h0]
  obtain ⟨c₀⟩ := hne
  obtain ⟨T, hT, hTS⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : AlgChart p σ D => c.e.source) fun c => c.e.open_source
  obtain ⟨ch, hch⟩ := (hT.insert c₀).exists_eq_range (Set.insert_nonempty _ _)
  set Q : ℕ → Set (CxPts p σ) := disjointed fun m => (ch m).e.source with hQdef
  set P : ℕ → Set (CxPts p σ) := fun m => S ∩ Q m with hPdef
  have hQm : ∀ m, MeasurableSet (Q m) :=
    MeasurableSet.disjointed fun m => (ch m).e.open_source.measurableSet
  have hPm : ∀ m, MeasurableSet (P m) := fun m => hS.inter (hQm m)
  have hPc : ∀ m, P m ⊆ (ch m).e.source := fun m => Set.inter_subset_right.trans (disjointed_subset _ m)
  have hPS : ∀ m, P m ⊆ S := fun m => Set.inter_subset_left
  have hPd : Pairwise (Function.onFun Disjoint P) := fun i j hij =>
    ((disjoint_disjointed _) hij).mono Set.inter_subset_right Set.inter_subset_right
  have hcov : ∀ τ : AlgChart p σ D → CxPts p σ → ℝ, part τ Sᶜ = 0 → part τ (⋃ m, P m)ᶜ = 0 := by
    intro τ hτ
    refine measure_mono_null (t := Sᶜ ∪ (⋃ c : AlgChart p σ D, c.e.source)ᶜ) ?_
      (measure_union_null hτ (part_compl_iUnion_source τ))
    intro y hy
    by_contra hc
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hc
    obtain ⟨hyS, hyU⟩ := hc
    apply hy
    have h1 : y ∈ ⋃ c ∈ T, c.e.source := by rw [hTS]; exact hyU
    obtain ⟨c', hc', hy'⟩ := Set.mem_iUnion₂.1 h1
    obtain ⟨m, rfl⟩ := hch.le (Set.mem_insert_of_mem _ hc')
    have h2 : y ∈ ⋃ m, Q m := by
      rw [hQdef, iUnion_disjointed]; exact Set.mem_iUnion.2 ⟨m, hy'⟩
    obtain ⟨m', hm'⟩ := Set.mem_iUnion.1 h2
    exact Set.mem_iUnion.2 ⟨m', hyS, hm'⟩
  have hsplit : ∀ (μ : Measure (CxPts p σ)) (g : CxPts p σ → ℝ≥0∞), μ (⋃ m, P m)ᶜ = 0 →
      ∫⁻ y, g y ∂μ = ∑' m, ∫⁻ y in P m, g y ∂μ := by
    intro μ g h
    have hr : μ.restrict (⋃ m, P m) = μ := Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 h)
    rw [← lintegral_iUnion hPm hPd, hr]

  set G : ℕ → ℝ → ℝ≥0∞ := fun m R =>
    ∫⁻ v in (ch m).e '' P m, ENNReal.ofReal |f R ((ch m).e.symm v) * ρ R (ch m) ((ch m).e.symm v)| with hGdef
  set B : ℕ → ℝ≥0∞ := fun m => ∫⁻ y in P m, ENNReal.ofReal (F y) ∂part w with hBdef
  have hE : ∀ m, MeasurableSet ((ch m).e '' P m) := fun m => ChartGlue.measurableSet_image _ (hPm m) (hPc m)
  have hEt : ∀ m, (ch m).e '' P m ⊆ (ch m).e.target := fun m =>
    (Set.image_mono (hPc m)).trans (ch m).e.image_source_eq_target.subset
  have hFm : ∀ m, AEMeasurable (fun y => ENNReal.ofReal (F y)) ((part w).restrict (P m)) := fun m =>
    hF.1.aemeasurable.ennreal_ofReal.restrict
  have hBchart : ∀ m, B m = ∫⁻ v in (ch m).e '' P m,
      ENNReal.ofReal (w (ch m) ((ch m).e.symm v)) * ENNReal.ofReal (F ((ch m).e.symm v)) := fun m =>
    setLIntegral_part_chart hw (ch m) (hPm m) (hPc m) (hFm m)
  have hBsum : ∑' m, B m ≠ ⊤ := by
    rw [hBdef, ← lintegral_iUnion hPm hPd]
    exact ne_top_of_le_ne_top hF.lintegral_lt_top.ne (setLIntegral_le_lintegral _ _)
  have hpb : ∀ᶠ R in atTop, ∀ m, ∀ᵐ v ∂(volume.restrict ((ch m).e '' P m)),
      ENNReal.ofReal |f R ((ch m).e.symm v) * ρ R (ch m) ((ch m).e.symm v)| ≤
        ENNReal.ofReal (w (ch m) ((ch m).e.symm v)) * ENNReal.ofReal (F ((ch m).e.symm v)) := by
    filter_upwards [hdom] with R hR m
    refine ae_restrict_of_forall_mem (hE m) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [(ch m).e.left_inv (hPc m hy), ← ENNReal.ofReal_mul' (hF0 y), mul_comm (w (ch m) y)]
    exact ENNReal.ofReal_le_ofReal (hR (ch m) y (hPc m hy) (hPS m hy))
  have hGB : ∀ᶠ R in atTop, ∀ m, G m R ≤ B m := by
    filter_upwards [hpb] with R hR m
    rw [hBchart m]
    exact lintegral_mono_ae (hR m)
  have hG0 : ∀ m, Tendsto (G m) atTop (𝓝 0) := by
    intro m
    have hsym : AEMeasurable (ch m).e.symm (volume.restrict ((ch m).e '' P m)) :=
      ((ch m).e.continuousOn_symm.mono (hEt m)).aemeasurable (hE m)
    have hl : ∀ᵐ v ∂(volume.restrict ((ch m).e '' P m)), Tendsto
        (fun R => ENNReal.ofReal |f R ((ch m).e.symm v) * ρ R (ch m) ((ch m).e.symm v)|) atTop (𝓝 0) := by
      refine ae_restrict_of_forall_mem (hE m) ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [(ch m).e.left_inv (hPc m hy)]
      simpa using ENNReal.tendsto_ofReal (hlim (ch m) y (hPc m hy) (hPS m hy)).abs
    have := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume.restrict ((ch m).e '' P m))
      (F := fun R v => ENNReal.ofReal |f R ((ch m).e.symm v) * ρ R (ch m) ((ch m).e.symm v)|)
      (f := fun _ => 0)
      (fun v => ENNReal.ofReal (w (ch m) ((ch m).e.symm v)) * ENNReal.ofReal (F ((ch m).e.symm v)))
      (Eventually.of_forall fun R => (continuous_abs.measurable.comp_aemeasurable
        (((hf R).comp_aemeasurable hsym).mul ((((hρ R).2 (ch m)).mono (hEt m)).aemeasurable (hE m)))).ennreal_ofReal)
      (hpb.mono fun R hR => hR m)
      (by rw [← hBchart m]; exact ne_top_of_le_ne_top hBsum (ENNReal.le_tsum m))
      hl
    simpa only [lintegral_zero] using this
  have hΦ : Tendsto (fun R => ∑' m, G m R) atTop (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := Measure.count) (F := fun R m => G m R)
      (f := fun _ => 0) B (Eventually.of_forall fun R => measurable_from_nat)
      (hGB.mono fun R hR => ae_of_all _ hR) (by rwa [lintegral_count])
      (ae_of_all _ hG0)
    simpa only [lintegral_count, lintegral_zero] using this
  have hab : ∀ R, ∫⁻ y, ENNReal.ofReal ‖f R y‖ ∂part (ρ R) +
      ∫⁻ y, ENNReal.ofReal ‖f R y‖ ∂part (fun c y => -ρ R c y) ≤ ∑' m, G m R := by
    intro R
    have hg : Measurable fun y => ENNReal.ofReal ‖f R y‖ := (hf R).norm.ennreal_ofReal
    rw [hsplit _ _ (hcov _ (hSρ R).1), hsplit _ _ (hcov _ (hSρ R).2), ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun m => ?_
    rw [setLIntegral_part_chart (isMDens_of_isDens (hρ R)) (ch m) (hPm m) (hPc m) hg.aemeasurable,
      setLIntegral_part_chart (isMDens_neg (isMDens_of_isDens (hρ R))) (ch m) (hPm m) (hPc m) hg.aemeasurable]
    exact (le_lintegral_add _ _).trans (lintegral_mono fun v => (ofReal_mul_add_ofReal_neg_mul _ _).le)
  have ha : Tendsto (fun R => ∫⁻ y, ENNReal.ofReal ‖f R y‖ ∂part (ρ R)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hΦ (fun R => bot_le)
      fun R => le_self_add.trans (hab R)
  have hb : Tendsto (fun R => ∫⁻ y, ENNReal.ofReal ‖f R y‖ ∂part (fun c y => -ρ R c y)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hΦ (fun R => bot_le)
      fun R => le_add_self.trans (hab R)
  have hlim2 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ha).add
    ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hb)
  simp only [ENNReal.toReal_zero, add_zero] at hlim2
  refine squeeze_zero_norm (fun R => ?_) hlim2
  simp only [Function.comp_apply]
  exact (norm_sub_le _ _).trans (add_le_add (norm_integral_le_lintegral_norm _) (norm_integral_le_lintegral_norm _))
