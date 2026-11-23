import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackIsPotentialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticoneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNullStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatioStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPointStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

section Abstract
open Set
open scoped ENNReal
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.FinChart

namespace GlobalTheory.CompanionTheory.ArchDom

theorem measurableSet_inter_preimage {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {f : α → β} {s : Set α}
    {t : Set β} (hf : ContinuousOn f s) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ f ⁻¹' t) := by
  have hm : Measurable (s.restrict f) := (continuousOn_iff_continuous_restrict.1 hf).measurable
  have := hs.subtype_image (hm ht)
  convert this using 1
  ext v
  exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩

theorem chartMeas_le_sum {D n : ℕ} {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (e : OpenPartialHomeomorph Y (V D)) (ρ : Y → ℝ≥0∞) {Z : Set Y}
    (hZ : MeasurableSet Z) (hnull : volume (e.target ∩ e.symm ⁻¹' Z) = 0)
    (P : Fin n → (Fin D → ℂ) → Y) (K : Fin n → Set (Fin D → ℂ)) (hK : ∀ j, MeasurableSet (K j))
    (hP : ∀ j, ContinuousOn (P j) (K j)) (w : Fin n → (Fin D → ℂ) → ℝ≥0∞)
    (hcov : ∀ y ∈ e.source, y ∉ Z → ∃ j, ∃ u ∈ K j, P j u = y)
    (hinj : ∀ j, ∀ u ∈ K j, ∀ u' ∈ K j, P j u ∉ Z → P j u = P j u' → u = u')
    (hdet : ∀ j, ∀ u ∈ K j, P j u ∈ e.source → P j u ∉ Z →
      DifferentiableAt ℝ ((toV D).symm ∘ e ∘ P j) u ∧
      ENNReal.ofReal |(fderiv ℝ ((toV D).symm ∘ e ∘ P j) u).det| * ρ (P j u) ≤ w j u) :
    GlobalTheory.ChartGlue.chartMeas e ρ ≤
      ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) := by
  refine Measure.le_iff.2 fun S hS => ?_
  have hsrc := e.open_source.measurableSet
  let T : Fin n → Set (Fin D → ℂ) := fun j => K j ∩ P j ⁻¹' ((e.source ∩ S) \ Z)
  let G : Fin n → (Fin D → ℂ) → (Fin D → ℂ) := fun j => (toV D).symm ∘ e ∘ P j
  have hT : ∀ j, MeasurableSet (T j) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) ((hsrc.inter hS).diff hZ)
  have hM : ∀ j, MeasurableSet (K j \ P j ⁻¹' Z) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) hZ.compl
  have hcover : e '' (e.source ∩ S) ⊆
      (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j) := by
    rintro _ ⟨y, ⟨hy, hyS⟩, rfl⟩
    by_cases hyZ : y ∈ Z
    · exact Or.inl (GlobalTheory.ChartGlue.mem_over e hy hyZ)
    · obtain ⟨j, u, hu, rfl⟩ := hcov y hy hyZ
      refine Or.inr (mem_iUnion.2 ⟨j, _, ⟨u, ⟨hu, ⟨⟨hy, hyS⟩, hyZ⟩⟩, rfl⟩, ?_⟩)
      simp [G]
  have hterm : ∀ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) ≤
      Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S := by
    intro j
    have hinjG : InjOn (G j) (T j) := by
      rintro u ⟨hu, hR⟩ u' ⟨hu', hR'⟩ h
      have h1 : e (P j u) = e (P j u') := (toV D).symm.injective h
      exact hinj j u hu u' hu' hR.2 (e.injOn hR.1.1 hR'.1.1 h1)
    have hder : ∀ u ∈ T j, HasFDerivWithinAt (G j) (fderiv ℝ (G j) u) (T j) u := fun u hu =>
      (hdet j u hu.1 hu.2.1.1 hu.2.2).1.hasFDerivAt.hasFDerivWithinAt
    have hae : AEMeasurable (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) :=
      (((hP j).mono diff_subset).aemeasurable (hM j)).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [← measurePreserving_toV.setLIntegral_comp_emb (toV D).toHomeomorph.measurableEmbedding,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hT j) hder hinjG,
      Measure.map_apply_of_aemeasurable hae hS, withDensity_apply',
      Measure.restrict_restrict' (hM j)]
    refine (setLIntegral_mono' (hT j) fun u hu => ?_).trans (lintegral_mono_set ?_)
    · have hv : toV D (G j u) = e (P j u) := (toV D).apply_symm_apply _
      have := (hdet j u hu.1 hu.2.1.1 hu.2.2).2
      rw [hv, e.left_inv hu.2.1.1]
      exact this
    · rintro u ⟨hu, hR⟩
      exact ⟨hR.1.2, hu, hR.2⟩
  calc GlobalTheory.ChartGlue.chartMeas e ρ S = ∫⁻ v in e '' (e.source ∩ S), ρ (e.symm v) :=
        GlobalTheory.ChartGlue.chartMeas_apply e ρ hS
    _ ≤ ∫⁻ v in (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ v in e.target ∩ e.symm ⁻¹' Z, ρ (e.symm v)) +
          ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := lintegral_union_le _ _ _
    _ = ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := by
        rw [setLIntegral_measure_zero _ _ hnull, zero_add]
    _ ≤ ∑' j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := lintegral_iUnion_le _ _
    _ = ∑ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := tsum_fintype _
    _ ≤ ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by rw [Measure.finset_sum_apply]

theorem ofReal_abs_norm_mul_le (d : ℂ) (x : ℝ) (ε : ℤˣ) :
    ENNReal.ofReal |Algebra.norm ℝ d| * ENNReal.ofReal ((ε : ℤ) * x) ≤
      ENNReal.ofReal |‖d‖ ^ 2 * x| := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity), abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖d‖ ^ 2)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using le_abs_self x
  · simpa using neg_le_abs x

end GlobalTheory.CompanionTheory.ArchDom
end Abstract

open GlobalTheory.FinChart in

theorem GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) →
    (∀ y, y ∉ Z → ∃ x, F x = y) → (∀ x x', F x ∉ Z → F x = F x' → x = x') →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (ε : ℤˣ) (K : Fin A.n → Set (Fin D → ℂ)),
    (∀ j, IsCompact (K j)) → (∀ j, K j ⊆ (A.chart j).target) →
    (∀ x, ∃ j, ∃ u ∈ K j, (A.chart j).symm u = x) →
    φ.chernPart D ε ≤ ∑ j, Measure.map (F ∘ (A.chart j).symm)
      ((volume.restrict (K j \ (F ∘ (A.chart j).symm) ⁻¹' Z)).withDensity fun u =>
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|) := by
  intro k _ X q σ D T _ A F hF hol Z hZ hnull hsurj hinj B φ hφ ε K hK hKt hKc
  refine iSup_le fun c => ?_
  refine GlobalTheory.CompanionTheory.ArchDom.chartMeas_le_sum c.e _ hZ (hnull c) (fun j => F ∘ (A.chart j).symm) K
    (fun j => (hK j).measurableSet)
    (fun j => hF.comp_continuousOn ((A.chart j).continuousOn_symm.mono (hKt j))) _ ?_ ?_ ?_
  · intro y _ hyZ
    obtain ⟨x, rfl⟩ := hsurj y hyZ
    obtain ⟨j, u, hu, rfl⟩ := hKc x
    exact ⟨j, u, hu, rfl⟩
  · intro j u hu u' hu' hZu h
    exact (A.chart j).symm.injOn (hKt j hu) (hKt j hu') (hinj _ _ hZu h)
  · intro j u hu hsrc _
    obtain ⟨han, hd⟩ := GlobalTheory.T.smooth_weight_pullback_chart_formula A F hF hol φ hφ c j u (hKt j hu) hsrc
    have hG : (toV D).symm ∘ c.e ∘ (F ∘ (A.chart j).symm) =
        c.finChart ∘ F ∘ (A.chart j).symm := rfl
    rw [hG]
    have hdiff := han.differentiableAt
    refine ⟨hdiff.restrictScalars ℝ, ?_⟩
    have hdet : (fderiv ℝ (c.finChart ∘ F ∘ (A.chart j).symm) u).det = Algebra.norm ℝ
        (LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) := by
      rw [hdiff.fderiv_restrictScalars ℝ]
      exact LinearMap.det_restrictScalars
        (f := (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, hd]
    exact GlobalTheory.CompanionTheory.ArchDom.ofReal_abs_norm_mul_le _ _ ε
