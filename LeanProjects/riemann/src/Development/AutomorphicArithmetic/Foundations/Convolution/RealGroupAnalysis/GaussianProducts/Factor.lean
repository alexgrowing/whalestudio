import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.factor :
    ∀ (X Y : Type) [TopologicalSpace X] [SigmaCompactSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (r : X → Y) (H : X → ℂ), Continuous r → Continuous H → (∀ x x', r x = r x' → H x = H x') → ∃ h : Y → ℂ, Measurable h ∧ ∀ x, h (r x) = H x := by
  intro X Y _ _ _ _ _ _ r H hr hH hf
  have key : ∀ F : Set X, IsClosed F → MeasurableSet (r '' F) := by
    intro F hF
    have e : r '' F = ⋃ n, r '' (F ∩ compactCovering X n) := by
      rw [← Set.image_iUnion, ← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
    rw [e]
    refine MeasurableSet.iUnion fun n => ?_
    exact (((isCompact_compactCovering X n).inter_left hF).image hr).isClosed.measurableSet
  have hrange : MeasurableSet (Set.range r) := by
    rw [← Set.image_univ]
    exact key _ isClosed_univ
  let h : Y → ℂ := fun y => if hy : ∃ x, r x = y then H hy.choose else 0
  have hh : ∀ x, h (r x) = H x := by
    intro x
    have hy : ∃ x', r x' = r x := ⟨x, rfl⟩
    simp only [h, dif_pos hy]
    exact hf _ _ hy.choose_spec
  refine ⟨h, measurable_of_isClosed fun C hC => ?_, hh⟩
  have himg : MeasurableSet (r '' (H ⁻¹' C)) := key _ (hC.preimage hH)
  have hout : ∀ y, y ∉ Set.range r → h y = 0 := by
    intro y hy
    have hy' : ¬ ∃ x, r x = y := hy
    simp only [h, dif_neg hy']
  by_cases h0 : (0 : ℂ) ∈ C
  · have e : h ⁻¹' C = r '' (H ⁻¹' C) ∪ (Set.range r)ᶜ := by
      ext y
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range r
        · obtain ⟨x, rfl⟩ := hyr
          refine Or.inl ⟨x, ?_, rfl⟩
          have : h (r x) ∈ C := hy
          rw [hh] at this
          exact this
        · exact Or.inr hyr
      · rintro (⟨x, hx, rfl⟩ | hy)
        · show h (r x) ∈ C
          rw [hh]
          exact hx
        · show h y ∈ C
          rw [hout y hy]
          exact h0
    rw [e]
    exact himg.union hrange.compl
  · have e : h ⁻¹' C = r '' (H ⁻¹' C) := by
      ext y
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range r
        · obtain ⟨x, rfl⟩ := hyr
          refine ⟨x, ?_, rfl⟩
          have : h (r x) ∈ C := hy
          rw [hh] at this
          exact this
        · have : h y ∈ C := hy
          rw [hout y hyr] at this
          exact absurd this h0
      · rintro ⟨x, hx, rfl⟩
        show h (r x) ∈ C
        rw [hh]
        exact hx
    rw [e]
    exact himg
