import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

open MeasureTheory Topology
open scoped ENNReal

private theorem UpperTheory.ConvolutionTheory.G.uni_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [LocallyCompactSpace G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G']
    {μ : Measure G} {μ' : Measure G'} (h : UpperTheory.ConvolutionTheory.G.Uni μ) (h' : UpperTheory.ConvolutionTheory.G.Uni μ') :
    UpperTheory.ConvolutionTheory.G.Uni (μ.prod μ') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨inferInstance, ⟨?_⟩⟩
  have e : (Inv.inv : G × G' → G × G') = Prod.map Inv.inv Inv.inv := rfl
  rw [Measure.inv_def, e, ← Measure.map_prod_map _ _ measurable_inv measurable_inv,
    Measure.map_inv_eq_self, Measure.map_inv_eq_self]

theorem UpperTheory.ConvolutionTheory.G.quotProd_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotProd := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν hP μ' j' ν' hP'
  have hPP : UpperTheory.ConvolutionTheory.G.Pair (μ.prod μ') (j.prodMap j') (ν.prod ν') :=
    ⟨UpperTheory.ConvolutionTheory.G.uni_prod hP.1 hP'.1, hP.2.1.prodMap hP'.2.1, UpperTheory.ConvolutionTheory.G.uni_prod hP.2.2 hP'.2.2⟩
  refine ⟨hPP, fun F F' hF hFi hF' hFi' => ?_⟩
  obtain ⟨ρ, hc, hρ, -⟩ := hN G T μ j ν hP
  obtain ⟨ρ', hc', hρ', -⟩ := hN G' T' μ' j' ν' hP'
  haveI := hP.1.1
  haveI := hP'.1.1
  haveI := hP.2.2.1
  haveI := hP'.2.2.1
  have hj : Measurable j := hP.2.1.continuous.measurable
  have hj' : Measurable j' := hP'.2.1.continuous.measurable
  have hρρ : UpperTheory.ConvolutionTheory.G.IsNrm (j.prodMap j') (ν.prod ν')
      (fun g : G × G' => (ρ g.1 : ℝ≥0∞) * (ρ' g.2 : ℝ≥0∞)) := by
    refine ⟨(hρ.1.comp measurable_fst).mul (hρ'.1.comp measurable_snd), fun x => ?_⟩
    have := lintegral_prod_mul (μ := ν) (ν := ν') (f := fun t => (ρ (j t * x.1) : ℝ≥0∞))
      (g := fun t => (ρ' (j' t * x.2) : ℝ≥0∞))
      (hρ.1.comp (hj.mul_const _)).aemeasurable (hρ'.1.comp (hj'.mul_const _)).aemeasurable
    rw [hρ.2 x.1, hρ'.2 x.2, mul_one] at this
    exact this
  have hm : Measurable (fun g : G × G' => F g.1 * F' g.2) :=
    (hF.comp measurable_fst).mul (hF'.comp measurable_snd)
  have hi : ∀ (t : T × T') (g : G × G'),
      (fun g : G × G' => F g.1 * F' g.2) (j.prodMap j' t * g) = (fun g : G × G' => F g.1 * F' g.2) g := by
    intro t g
    show F (j t.1 * g.1) * F' (j' t.2 * g.2) = _
    rw [hFi, hFi']
  obtain ⟨a1, -, a3⟩ := hE G T μ j ν hP F hF hFi _ hρ
  obtain ⟨b1, -, b3⟩ := hE G' T' μ' j' ν' hP' F' hF' hFi' _ hρ'
  obtain ⟨c1, -, c3⟩ := hE (G × G') (T × T') _ _ _ hPP _ hm hi _ hρρ
  have key : (fun x : G × G' => F x.1 * F' x.2 * ((((ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)).toReal : ℝ) : ℂ)) =
      fun x : G × G' => (F x.1 * (((ρ x.1 : ℝ≥0∞).toReal : ℝ) : ℂ)) * (F' x.2 * (((ρ' x.2 : ℝ≥0∞).toReal : ℝ) : ℂ)) := by
    funext x
    rw [ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  refine ⟨fun h h' => ?_, ?_⟩
  · rw [c1, key]
    exact (a1.1 h).mul_prod (b1.1 h')
  · rw [c3, key, a3, b3]
    exact integral_prod_mul (fun x => F x * (((ρ x : ℝ≥0∞).toReal : ℝ) : ℂ))
      (fun x => F' x * (((ρ' x : ℝ≥0∞).toReal : ℝ) : ℂ))
