import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnComplexHessianOfContDiffOnTwo

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ENNReal

namespace GlobalTheory.HSAmp

theorem exists_isRatio_chernInt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ (L : HermLB p), L.SemiPos D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D),
    ∃ ρ : CxPts p σ → ℝ, ω.IsRatio (L.φ σ) ρ ∧ (∀ y, 0 ≤ ρ y) ∧ ∀ f : CxPts p σ → ℝ, Continuous f →
      (L.φ σ).chernInt D Set.univ f = ∫ y, f y * ρ y ∂ω.meas := by
  intro k _ X _ p D hX hG L hL σ ω
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hG σ
  have hcov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source := fun y =>
    have ⟨i, hi⟩ := R.cover y
    ⟨R.chart i, hi⟩
  choose c₀ hc₀ using hcov
  let ρ : CxPts p σ → ℝ := fun y => (c₀ y).chernDens (L.φ σ) y / ω.dens (c₀ y) y
  have key : ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, c.chernDens (L.φ σ) y = ρ y * ω.dens c y := by
    intro c y hy
    have hpos := ω.pos (c₀ y) y (hc₀ y)
    rw [c.chernDens_trans (c₀ y) (L.cInf σ) hy (hc₀ y), ω.trans c (c₀ y) y hy (hc₀ y)]
    simp only [ρ]
    field_simp
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y =>
    div_nonneg ((c₀ y).chernDens_nonneg (L.cInf σ) (hL σ) (hc₀ y)) (ω.pos _ _ (hc₀ y)).le

  have hρc : Continuous ρ := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    set c := c₀ y
    set i := pick (L.φ σ).isLB y
    have hyi : y ∈ ptsIn p σ (L.B.U i) := mem_pick _ y
    set O : Set (CxPts p σ) := c.e.source ∩ ptsIn p σ (L.B.U i) with hO
    have hOo : IsOpen O := c.e.open_source.inter (isOpen_ptsIn _)
    have hyO : y ∈ O := ⟨hc₀ y, hyi⟩
    set U' : Set (V D) := c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (L.B.U i)
    have hU' : IsOpen U' := isOpen_over c.e (isOpen_ptsIn _)
    have h2 : ContDiffOn ℝ 2 (fun v => (L.φ σ).φ i (c.e.symm v)) U' :=
      (contDiffOn_chart ((L.cInf σ) i) c).of_le (by norm_cast)
    have hmap : Set.MapsTo c.e O U' := fun z hz => mem_over c.e hz.1 hz.2
    have hent : ∀ a b, ContinuousOn (fun z => c.hess (L.φ σ) i z a b) O := fun a b =>
      (continuousOn_cHess_of_contDiffOn_two D U' _ hU' h2 a b).comp (c.e.continuousOn.mono fun z hz => hz.1) hmap
    have hdet : ContinuousOn (fun z => c.chernDens (L.φ σ) z) O := by
      have hm : ContinuousOn (fun z => c.hess (L.φ σ) i z) O :=
        continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => hent a b
      have hc : Continuous fun M : Matrix (Fin D) (Fin D) ℂ => (D.factorial / Real.pi ^ D : ℝ) * M.det.re :=
        continuous_const.mul (Complex.continuous_re.comp continuous_id.matrix_det)
      refine (hc.comp_continuousOn hm).congr fun z hz => ?_
      exact c.chernDens_eq (L.cInf σ) hz.1 hz.2
    have hq : ContinuousOn (fun z => c.chernDens (L.φ σ) z / ω.dens c z) O :=
      hdet.div ((ω.cont c).mono fun z hz => hz.1) fun z hz => (ω.pos c z hz.1).ne'
    refine (hq.congr fun z hz => ?_).continuousAt (hOo.mem_nhds hyO)
    rw [key c z hz.1, mul_div_cancel_right₀ _ (ω.pos c z hz.1).ne']
  have hm : Measurable fun y => ENNReal.ofReal (ρ y) := hρc.measurable.ennreal_ofReal
  have hneg : (L.φ σ).chernPart D (-1) = 0 := Weight.chernPart_neg_eq_zero (L.cInf σ) (hL σ)
  have hmeas : (L.φ σ).chernPart D 1 = ω.meas.withDensity fun y => ENNReal.ofReal (ρ y) := by
    refine ext_of_cover (fun c : AlgChart p σ D => c.e.source) (fun c => c.e.open_source)
      (fun y => ⟨c₀ y, hc₀ y⟩) fun c A hA hAc => ?_
    have hr : ω.meas.restrict A = (chartMeas c.e fun y => ENNReal.ofReal (ω.dens c y)).restrict A := by
      ext T hT
      rw [Measure.restrict_apply hT, Measure.restrict_apply hT, VolDens.meas,
        glueMeas_apply _ _ (fun a a' => a.holo_trans a') (fun a a' z hz hz' => by
          rw [ω.trans a a' z hz hz', ENNReal.ofReal_mul (sq_nonneg _)]) c (hT.inter hA)
          (Set.inter_subset_right.trans hAc)]
    have hsy : AEMeasurable c.e.symm (volume.restrict c.e.target) :=
      c.e.continuousOn_symm.aemeasurable c.e.open_target.measurableSet
    have hdm : AEMeasurable ((fun y => ENNReal.ofReal (ω.dens c y)) ∘ c.e.symm) (volume.restrict c.e.target) :=
      (ENNReal.continuous_ofReal.comp_continuousOn ((ω.cont c).comp c.e.continuousOn_symm
        fun v hv => c.e.map_target hv)).aemeasurable c.e.open_target.measurableSet
    have hI := measurableSet_image c.e hA hAc
    have hIt : c.e '' A ⊆ c.e.target := by rintro _ ⟨z, hz, rfl⟩; exact c.e.map_source (hAc hz)
    rw [Weight.chernPart_apply (L.cInf σ) 1 c hA hAc, withDensity_apply _ hA, hr, ← lintegral_indicator hA, chartMeas,
      lintegral_map' (hm.indicator hA).aemeasurable (hsy.mono_ac (withDensity_absolutelyContinuous _ _)),
      lintegral_withDensity_eq_lintegral_mul₀ hdm (g := fun v => A.indicator (fun y => ENNReal.ofReal (ρ y)) (c.e.symm v))
        ((hm.indicator hA).comp_aemeasurable hsy),
      ← Set.inter_eq_left.2 hIt, ← Measure.restrict_restrict hI, ← lintegral_indicator hI]
    refine setLIntegral_congr_fun c.e.open_target.measurableSet fun v hv => ?_
    by_cases hvA : c.e.symm v ∈ A
    · have hvI : v ∈ c.e '' A := ⟨_, hvA, c.e.right_inv hv⟩
      simp only [Set.indicator_of_mem hvI, Pi.mul_apply, Set.indicator_of_mem hvA, Function.comp_apply,
        Units.val_one, Int.cast_one, one_mul]
      rw [key c _ (hAc hvA), ENNReal.ofReal_mul (hρ0 _), mul_comm]
    · have hvI : v ∉ c.e '' A := by
        rintro ⟨z, hz, rfl⟩
        exact hvA (by rwa [c.e.left_inv (hAc hz)])
      simp only [Set.indicator_of_notMem hvI, Pi.mul_apply, Set.indicator_of_notMem hvA, mul_zero]
  refine ⟨ρ, ⟨hρc, key⟩, hρ0, fun f _ => ?_⟩
  have hn : Measurable fun y => (ρ y).toNNReal := hρc.measurable.real_toNNReal
  rw [Weight.chernInt, hneg, Measure.restrict_univ, Measure.restrict_univ, integral_zero_measure, sub_zero, hmeas]
  change ∫ y, f y ∂ω.meas.withDensity (fun y => ((ρ y).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hn]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hρ0 y), smul_eq_mul]
  exact mul_comm _ _

end GlobalTheory.HSAmp
