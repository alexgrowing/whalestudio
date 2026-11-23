import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb bas)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.FinChart
open scoped ContDiff ENNReal

namespace GlobalTheory

namespace FinChart

variable {D : ℕ}

theorem cHess_eq_hessC {f : V D → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f (toV D z)) :
    cHess D (fun v => (f v : ℂ)) (toV D z) = hessC (f ∘ toV D) z := by
  set x := toV D z with hx
  set H := fderiv ℝ (fderiv ℝ f) x with hH
  have hD : HasFDerivAt (fderiv ℝ f) H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have h₁ : fderiv ℝ (f ∘ toV D) =
      fun w => (fderiv ℝ f (toV D w)).comp (toV D).toContinuousLinearMap :=
    funext fun _ => (toV D).comp_right_fderiv
  have h₂ (u w : Fin D → ℂ) : fderiv ℝ (fderiv ℝ (f ∘ toV D)) z u w = H (toV D u) (toV D w) := by
    have := ((hD.comp z (toV D).hasFDerivAt).clm_comp
      (hasFDerivAt_const (toV D).toContinuousLinearMap z)).fderiv
    rw [h₁]
    erw [this]
    simp
  have hdiff := ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf
  set G : Fin D → V D → ℂ := fun l y => (2 : ℂ)⁻¹ *
    ((fderiv ℝ f y (bas D l) : ℂ) + Complex.I * (fderiv ℝ f y (Complex.I • bas D l) : ℂ))
  have hwdb (l) : wdb D l (fun y => (f y : ℂ)) =ᶠ[𝓝 x] G l := by
    filter_upwards [hdiff] with y hy
    simp only [wdb, G, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy]
    ring
  have hGd (l e) : fderiv ℝ (G l) x e =
      ((H e (bas D l) : ℂ) + Complex.I * (H e (Complex.I • bas D l) : ℂ)) / 2 := by
    have ha (b : V D) : HasFDerivAt (fun y => ((fderiv ℝ f y b : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((fderiv ℝ f x).comp (0 : V D →L[ℝ] V D) + H.flip b)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (hD.clm_apply (hasFDerivAt_const b x))
    have hG : HasFDerivAt (G l) _ x :=
      ((ha (bas D l)).add ((ha (Complex.I • bas D l)).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    rw [hG.fderiv]
    simp
    ring
  ext j l
  have b₁ (a : Fin D) : toV D (Pi.single a 1) = bas D a := rfl
  have b₂ (a : Fin D) : toV D (Complex.I • Pi.single a 1) = Complex.I • bas D a := rfl
  simp only [cHess, Matrix.of_apply, wd, (hwdb l).fderiv_eq, hGd, hessC, h₂, b₁, b₂]
  push_cast
  linear_combination (-(H (Complex.I • bas D j) (Complex.I • bas D l) : ℂ) / 4) * Complex.I_mul_I

theorem measurePreserving_toV : MeasurePreserving (toV D) :=
  MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
    (volume_preserving_ofLp_complex (Fin D))

end FinChart

section Abstract

variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem integrableOn_source_iff_of_density (c : OpenPartialHomeomorph X (Fin e → ℂ))
    {μ : Measure X} {w : (Fin e → ℂ) → ℝ} (hw : ContinuousOn w c.target)
    (hw0 : ∀ y ∈ c.target, 0 ≤ w y) (hμ : ∀ S, MeasurableSet S → S ⊆ c.source →
      μ S = ∫⁻ y in c.target ∩ c.symm ⁻¹' S, ENNReal.ofReal (w y))
    {g : X → ℝ} (hg : Measurable g) :
    (IntegrableOn g c.source μ ↔ IntegrableOn (fun y => g (c.symm y) * w y) c.target) ∧
      ∫ x in c.source, g x ∂μ = ∫ y in c.target, g (c.symm y) * w y := by
  have hT := c.open_target.measurableSet
  have key : μ.restrict c.source =
      ((volume.restrict c.target).withDensity fun y => ENNReal.ofReal (w y)).map c.symm := by
    ext S hS
    rw [Measure.restrict_apply hS, hμ _ (hS.inter c.open_source.measurableSet) inter_subset_right,
      Measure.map_apply_of_aemeasurable ((c.continuousOn_symm.aemeasurable hT).mono_ac
        (withDensity_absolutelyContinuous _ _)) hS, withDensity_apply',
      Measure.restrict_restrict' hT]
    congr 2
    ext y
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, c.map_target h.2⟩⟩
  rw [IntegrableOn, key]
  exact map_withDensity_integrable_integral c.open_target c.continuousOn_symm hw hw0 hg

theorem integrable_of_pieces (A : FinHolAtlas e X) (P : ChartPartition A) {μ : Measure X}
    {w : Fin A.n → (Fin e → ℂ) → ℝ} (hw : ∀ j, ContinuousOn (w j) (A.chart j).target)
    (hw0 : ∀ j, ∀ y ∈ (A.chart j).target, 0 ≤ w j y)
    (hμ : ∀ j S, MeasurableSet S → S ⊆ (A.chart j).source →
      μ S = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S, ENNReal.ofReal (w j y))
    {g : X → ℝ} (hg : Measurable g) (hi : ∀ j, IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w j y) (A.chart j).target) :
    Integrable g μ ∧ ∫ x, g x ∂μ = ∑ j, ∫ y in (A.chart j).target,
      P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w j y := by
  have hc (j) : Continuous (P.χ j) := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨l, hl⟩ := A.cover x
    have h₁ := ((P.smooth j l).continuousOn.mono fun y hy => ⟨hy, mem_univ _⟩).continuousAt
      ((A.chart l).open_target.mem_nhds ((A.chart l).map_source hl))
    refine (h₁.comp ((A.chart l).continuousAt hl)).congr ?_
    exact eventually_of_mem ((A.chart l).open_source.mem_nhds hl) fun z hz =>
      congrArg (P.χ j) ((A.chart l).left_inv hz)
  have key (j) := integrableOn_source_iff_of_density (A.chart j) (hw j) (hw0 j) (hμ j)
    ((hc j).measurable.mul hg)
  have h0 (j) (x) (hx : x ∉ (A.chart j).source) : P.χ j x * g x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (P.tsupport_subset j h), zero_mul]
  have h₁ (j) : Integrable (fun x => P.χ j x * g x) μ :=
    ((key j).1.2 (hi j)).integrable_of_forall_notMem_eq_zero (h0 j)
  have e : g = fun x => ∑ j, P.χ j x * g x := funext fun x => by
    rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
  refine ⟨e ▸ integrable_finsetSum _ fun j _ => h₁ j, ?_⟩
  conv_lhs => rw [e]
  rw [integral_finsetSum _ fun j _ => h₁ j]
  exact Finset.sum_congr rfl fun j _ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 j)).symm.trans (key j).2

end Abstract

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}
  {φ : Weight p σ B}

namespace Weight

theorem IsCInf.maDens_eq (h : φ.IsCInf) (c : AlgChart p σ D) {z : Fin D → ℂ}
    (hz : z ∈ c.finChart.target) :
    maDens (fun _ y => φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      c.chernDens φ (c.finChart.symm z) := by
  have hr : c.e (c.finChart.symm z) = toV D z := c.e.right_inv hz
  have hd := h.contDiffAt c (c.finChart.map_target hz) (mem_pick φ.isLB (c.finChart.symm z))
  rw [hr] at hd
  have e : (fun y => φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) = fun y => 2⁻¹ *
      ((fun v => φ.φ (pick φ.isLB (c.finChart.symm z)) (c.e.symm v)) ∘ toV D) y :=
    funext fun _ => div_eq_inv_mul _ _
  rw [maDens, ReciprocityTheory.AnForm.A.mdisc_const, e, hessC_const_mul', AlgChart.chernDens, AlgChart.hess,
    hr, cHess_eq_hessC hd, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Fintype.card_fin, ← mul_assoc, mul_assoc (D.factorial : ℝ), ← mul_pow, div_eq_mul_inv _ (_ ^ D),
    ← inv_pow]
  congr 3
  ring

variable {A : FinHolAtlas D (CxPts p σ)}

theorem IsCInf.locDens_eq (h : φ.IsCInf) (hA : IsAlgAtlas A) (j : Fin A.n) {z : Fin D → ℂ}
    (hz : z ∈ (A.chart j).target) : locDens A (fun _ => φ.locPot) j z =
      (hA.anRead.chart j).chernDens φ ((A.chart j).symm z) := by
  unfold locDens
  rw [hA.chart_eq j] at hz ⊢
  exact h.maDens_eq _ hz

theorem IsCInf.chernPart_eq [SecondCountableTopology (CxPts p σ)] (h : φ.IsCInf)
    (hA : IsAlgAtlas A) (ε : ℤˣ) (j : Fin A.n) (S : Set (CxPts p σ)) (hS : MeasurableSet S)
    (hs : S ⊆ (A.chart j).source) : φ.chernPart D ε S =
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S,
        ENNReal.ofReal (max ((ε : ℤ) * locDens A (fun _ => φ.locPot) j y) 0) := by
  have hl (y) := h.locDens_eq hA j (z := y)
  generalize locDens A (fun _ => φ.locPot) j = d at hl ⊢
  rw [hA.chart_eq j] at hs hl ⊢
  set c := hA.anRead.chart j
  have hm := measurableSet_image c.e hS hs
  rw [chernPart_apply h ε c hS hs, ← measurePreserving_toV.setLIntegral_comp_preimage_emb
    (toV D).toHomeomorph.measurableEmbedding]
  have e : c.e '' S = c.e.target ∩ c.e.symm ⁻¹' S := by
    rw [← c.e.image_source_inter_eq', inter_eq_right.2 (show S ⊆ c.e.source from hs)]
  rw [e] at hm ⊢
  refine setLIntegral_congr_fun (hm.preimage (toV D).continuous.measurable) fun y hy => ?_
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_le, max_eq_left, hl y hy.1]
  rfl

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)]

theorem IsCInf.chernInt_eq_mInt_of_isAlgAtlas (h : φ.IsCInf) (hA : IsAlgAtlas A)
    {g : CxPts p σ → ℝ} (hg : Measurable g) :
    (φ.ChernIntegrableOn D univ g ↔ MIntegrable A (fun _ => φ.locPot) g) ∧
      (φ.ChernIntegrableOn D univ g → φ.chernInt D univ g = mInt A (fun _ => φ.locPot) g) := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set P := hne.some
  set d := locDens A fun _ => φ.locPot with hd
  have hdc (j) : ContinuousOn (d j) (A.chart j).target := locDensCont A _
    (fun _ => ((isCInf_iff_isSmooth hA.anRead).1 h).isPotential hA) j
  let w (ε : ℤˣ) (j) (y) : ℝ := max ((ε : ℤ) * d j y) 0
  have hw (ε j) : ContinuousOn (w ε j) (A.chart j).target :=
    (continuous_id.max continuous_const).comp_continuousOn (continuousOn_const.mul (hdc j))
  have hw0 (ε j) : ∀ y ∈ (A.chart j).target, 0 ≤ w ε j y := fun _ _ => le_max_right _ _
  have hsub (j y) : w 1 j y - w (-1) j y = d j y := by
    simpa [w] using max_zero_sub_max_neg_zero_eq_self (d j y)
  have habs (ε j y) : |w ε j y| ≤ |d j y| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ((le_abs_self _).trans_eq ?_) (abs_nonneg _)
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have back (hm : MIntegrable A (fun _ => φ.locPot) g) (ε j) : IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w ε j y)
      (A.chart j).target := by
    obtain ⟨hKc, hKs⟩ := image_closed_compact (A.chart j) (isClosed_tsupport (P.χ j))
      (P.tsupport_subset j)
    refine integrableOn_target_of_closed (A.chart j) (Z := tsupport (P.χ j))
      (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
    have hcc := (chi_comp_continuousOn P j).mono hKs
    refine Integrable.mono ((hm j _ hKs hKc).continuousOn_mul hcc hKc) ?_ (.of_forall fun y => ?_)
    · exact (((hcc.aemeasurable hKc.measurableSet).mul (hg.comp_aemeasurable
        (((A.chart j).continuousOn_symm.mono hKs).aemeasurable hKc.measurableSet))).mul
        (((hw ε j).mono hKs).aemeasurable hKc.measurableSet)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (habs ε j y) (by positivity)
  have pieces (hm : MIntegrable A (fun _ => φ.locPot) g) (ε) :=
    integrable_of_pieces A P (hw ε) (hw0 ε) (h.chernPart_eq hA ε) hg (back hm ε)
  have fwd (hi : φ.ChernIntegrableOn D univ g) : MIntegrable A (fun _ => φ.locPot) g :=
    fun j K hK _ => by
    have key (ε) := (integrableOn_source_iff_of_density (A.chart j) (hw ε j) (hw0 ε j)
      (h.chernPart_eq hA ε j) hg).1.1
    refine IntegrableOn.mono_set ?_ hK
    refine (Integrable.sub (key 1 (hi.1.mono_set (subset_univ _)))
      (key (-1) (hi.2.mono_set (subset_univ _)))).congr (.of_forall fun y => ?_)
    simp only [Pi.sub_apply, ← mul_sub, hsub, hd]
  refine ⟨⟨fwd, fun hm => ⟨(pieces hm 1).1.integrableOn, (pieces hm (-1)).1.integrableOn⟩⟩,
    fun hi => ?_⟩
  have hm := fwd hi
  rw [chernInt, Measure.restrict_univ, Measure.restrict_univ, (pieces hm 1).2, (pieces hm (-1)).2,
    mInt_eq_integralWith A _ hne, integralWith, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (back hm 1 j) (back hm (-1) j)]
  simp only [← mul_sub, hsub, hd, P]

theorem chernInt_eq_mInt (R : AnRead p σ D) (h : φ.IsCInf) {g : CxPts p σ → ℝ}
    (hg : Measurable g) :
    (φ.ChernIntegrableOn D univ g ↔ MIntegrable R.finAtlas (fun _ => φ.locPot) g) ∧
      (φ.ChernIntegrableOn D univ g →
        φ.chernInt D univ g = mInt R.finAtlas (fun _ => φ.locPot) g) :=
  h.chernInt_eq_mInt_of_isAlgAtlas R.isAlgAtlas_finAtlas hg

end Weight

end GlobalTheory
