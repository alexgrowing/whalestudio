import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters

namespace ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion

open NumberField Complex MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_fd (X : Data E r) (la : Wt X.Ψ r) :
    ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ := by
  let L : Submodule ℤ (X.Ψ → ℝ) := (X.periods la).toIntSubmodule
  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (X.periods la))
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using RealEmbeddingCharacters.periods_span (X := X) (la := la)⟩
  haveI := ZLattice.module_free ℝ L
  haveI := ZLattice.module_finite ℝ L
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := by
    show Submodule.span ℤ (Set.range ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) = L
    rw [Module.Basis.ofZLatticeBasis_span]
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, ?_, ?_, ?_⟩
  · have h := ZSpan.isAddFundamentalDomain b volume
    rw [hspan] at h
    exact h
  · exact pos_iff_ne_zero.2 (ZSpan.measure_fundamentalDomain_ne_zero b)
  · exact (ZSpan.fundamentalDomain_isBounded b).measure_lt_top

lemma integral_swap_of_bdd {m n : Type} [Fintype m] [Fintype n] {D : Set (m → ℝ)} {K : Set (n → ℝ)}
    (hD : volume D < ⊤) (hK : volume K < ⊤) {f : (m → ℝ) → (n → ℝ) → ℂ}
    (hf : Continuous (Function.uncurry f)) {M : ℝ} (hM : ∀ s t, ‖f s t‖ ≤ M) :
    ∫ s in D, ∫ t in K, f s t = ∫ t in K, ∫ s in D, f s t := by
  haveI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.2 hD.ne
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.ne
  apply MeasureTheory.integral_integral_swap
  exact Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hM p.1 p.2)

end

end ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
