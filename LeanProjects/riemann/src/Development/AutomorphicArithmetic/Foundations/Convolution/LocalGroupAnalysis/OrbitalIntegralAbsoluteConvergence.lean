import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open PositivityTheory.Rg.Tf.Geo
open MeasureTheory
open scoped ENNReal

private theorem finite_fiber_integral {X T : Type} [Group X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [Group T]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (i : T →* X) (Φ : X → ℂ) (ρ : X → NNReal) (hΦ : Continuous Φ)
    (hρ : Continuous ρ) (hC : ∃ C, IsCompact C ∧ ∀ x, Φ x ≠ 0 → ∃ t, ∃ y ∈ C, x = i t * y)
    (h : ∀ C : Set X, IsCompact C → ∃ C' : Set X, IsCompact C' ∧ ∀ t, ∀ x ∈ C, ρ (i t * x) ≠ 0 → i t * x ∈ C') :
    ∫⁻ x, ‖Φ x‖ₑ * (ρ x : ℝ≥0∞) ∂μ < ⊤ := by
  obtain ⟨C, hC, hs⟩ := hC
  obtain ⟨C', hC', hs'⟩ := h C hC
  have hc : Continuous fun x => Φ x * ((ρ x : ℝ) : ℂ) :=
    hΦ.mul (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hρ))
  have hk : HasCompactSupport fun x => Φ x * ((ρ x : ℝ) : ℂ) := by
    refine HasCompactSupport.intro hC' fun x hx => ?_
    by_contra hne
    have h1 : Φ x ≠ 0 := left_ne_zero_of_mul hne
    have h2 : ρ x ≠ 0 := by
      intro h0
      exact hne (by simp [h0])
    obtain ⟨t, y, hy, rfl⟩ := hs x h1
    exact hx (hs' t y hy h2)
  have hi := (hc.integrable_of_hasCompactSupport (μ := μ) hk).2
  unfold HasFiniteIntegral at hi
  convert hi using 3 with x
  rw [enorm_mul]
  congr 1
  simp [enorm]

private theorem prod_isInvInvariant {T T' : Type} [Group T] [MeasurableSpace T] [MeasurableInv T] [Group T'] [MeasurableSpace T']
    [MeasurableInv T'] (ν : Measure T) (ν' : Measure T') [SFinite ν] [SFinite ν'] [ν.IsInvInvariant] [ν'.IsInvInvariant] :
    (ν.prod ν').IsInvInvariant := by
  constructor
  exact ((Measure.measurePreserving_inv ν).prod (Measure.measurePreserving_inv ν')).map_eq

theorem UpperTheory.ConvolutionTheory.G.orbitalIntegral_absolute_convergence :
    Q1 → Q2 → Q3 := by
  intro h1 h2 X T X' T' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ μ' _ ν' _ _ _ _ _
    i i' hi hi' Φ Φ' hΦ hΦ' hinv hinv' hC hC'
  obtain ⟨ρ, hρ, hn, hs⟩ := h2 X T ν i hi
  obtain ⟨ρ', hρ', hn', hs'⟩ := h2 X' T' ν' i' hi'
  have f1 := finite_fiber_integral μ i Φ ρ hΦ hρ hC hs
  have f2 := finite_fiber_integral μ' i' Φ' ρ' hΦ' hρ' hC' hs'
  have e1 := h1 X X T μ ν (MonoidHom.id X) i measurable_id hi.continuous Φ _ hΦ.measurable hinv hn f1
  have e2 := h1 X' X' T' μ' ν' (MonoidHom.id X') i' measurable_id hi'.continuous Φ' _ hΦ'.measurable hinv' hn' f2
  haveI := prod_isInvInvariant ν ν'
  have hn3 : IsNormAlong id (fun t : T × T' => (i t.1, i' t.2)) (ν.prod ν')
      (fun x : X × X' => (ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)) := by
    refine ⟨(hn.1.comp measurable_fst).mul (hn'.1.comp measurable_snd), fun x => ?_⟩
    have a1 : Measurable fun t => (ρ (i t * x.1) : ℝ≥0∞) :=
      hn.1.comp (hi.continuous.mul continuous_const).measurable
    have a2 : Measurable fun t => (ρ' (i' t * x.2) : ℝ≥0∞) :=
      hn'.1.comp (hi'.continuous.mul continuous_const).measurable
    have := lintegral_prod_mul (μ := ν) (ν := ν') a1.aemeasurable a2.aemeasurable
    have b1 := hn.2 x.1
    have b2 := hn'.2 x.2
    simp only [id] at b1 b2
    rw [b1, b2, mul_one] at this
    exact this
  have f3 : ∫⁻ x : X × X', ‖Φ x.1 * Φ' x.2‖ₑ * ((ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)) ∂(μ.prod μ') < ⊤ := by
    have a1 : Measurable fun x => ‖Φ x‖ₑ * (ρ x : ℝ≥0∞) := hΦ.measurable.enorm.mul hn.1
    have a2 : Measurable fun x => ‖Φ' x‖ₑ * (ρ' x : ℝ≥0∞) := hΦ'.measurable.enorm.mul hn'.1
    have := lintegral_prod_mul (μ := μ) (ν := μ') a1.aemeasurable a2.aemeasurable
    refine lt_of_eq_of_lt ?_ (this ▸ ENNReal.mul_lt_top f1 f2)
    refine lintegral_congr fun x => ?_
    rw [enorm_mul]
    ring
  have e3 := h1 (X × X') (X × X') (T × T') (μ.prod μ') (ν.prod ν') (MonoidHom.id _) (i.prodMap i') measurable_id
    (hi.continuous.prodMap hi'.continuous) (fun x => Φ x.1 * Φ' x.2) _
    ((hΦ.measurable.comp measurable_fst).mul (hΦ'.measurable.comp measurable_snd))
    (fun t x => by
      show Φ (i t.1 * x.1) * Φ' (i' t.2 * x.2) = _
      rw [hinv, hinv']) hn3 f3
  refine e3.trans (Eq.trans ?_ (congrArg₂ (· * ·) e1 e2).symm)
  rw [← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [MonoidHom.id_apply, ENNReal.toReal_mul, Complex.ofReal_mul]
  ring
