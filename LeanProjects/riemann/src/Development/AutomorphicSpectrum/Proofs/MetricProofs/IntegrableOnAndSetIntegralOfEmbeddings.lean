import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Metric

theorem measure_eq_sum_map_of_embeddings {α : Type} [Fintype α] {Y : Type} [MeasurableSpace Y]
    {Z : α → Type} [∀ a, MeasurableSpace (Z a)] {s : ∀ a, Z a → Y}
    (hs : ∀ a, MeasurableEmbedding (s a)) (hu : ∀ y, ∃! a, y ∈ Set.range (s a))
    {ν : Measure Y} {μ : ∀ a, Measure (Z a)}
    (hν : ∀ a (S : Set (Z a)), MeasurableSet S → ν (s a '' S) = μ a S) :
    ν = ∑ a, Measure.map (s a) (μ a) := by
  ext T hT
  rw [Measure.finsetSum_apply]
  have hcover : T = ⋃ a, T ∩ Set.range (s a) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hy
      obtain ⟨a, ha, -⟩ := hu y
      exact ⟨a, hy, ha⟩
    · rintro ⟨a, hy, -⟩
      exact hy
  have hdisj : Pairwise (Function.onFun Disjoint fun a => T ∩ Set.range (s a)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨-, hya⟩ ⟨-, hyb⟩
    obtain ⟨a', -, ha'⟩ := hu y
    exact hab ((ha' a hya).trans (ha' b hyb).symm)
  have hmeas : ∀ a, MeasurableSet (T ∩ Set.range (s a)) := fun a =>
    hT.inter (hs a).measurableSet_range
  rw [show ν T = ν (⋃ a, T ∩ Set.range (s a)) by rw [← hcover], measure_iUnion hdisj hmeas,
    tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(hs a).map_apply, ← hν a _ ((hs a).measurable hT), Set.image_preimage_eq_inter_range]

theorem integrableOn_and_setIntegral_of_embeddings :
    ∀ (α : Type) [Finite α] (Y : Type) [MeasurableSpace Y] (Z : α → Type)
      [∀ a, MeasurableSpace (Z a)] (s : ∀ a, Z a → Y), (∀ a, MeasurableEmbedding (s a)) →
      (∀ y, ∃! a, y ∈ Set.range (s a)) → ∀ (ν : Measure Y) (μ : ∀ a, Measure (Z a)),
      (∀ a (S : Set (Z a)), MeasurableSet S → ν (s a '' S) = μ a S) →
      ∀ (S : Set Y), MeasurableSet S → ∀ f : Y → ℝ,
      (IntegrableOn f S ν ↔ ∀ a, IntegrableOn (fun z => f (s a z)) (s a ⁻¹' S) (μ a)) ∧
      (IntegrableOn f S ν →
        ∫ y in S, f y ∂ν = ∑ᶠ a, ∫ z in s a ⁻¹' S, f (s a z) ∂(μ a)) := by
  intro α _ Y _ Z _ s hs hu ν μ hν S hS f
  haveI := Fintype.ofFinite α
  have hνeq := measure_eq_sum_map_of_embeddings hs hu hν
  have hres : ν.restrict S = ∑ a, (Measure.map (s a) (μ a)).restrict S := by
    ext T hT
    rw [hνeq, Measure.restrict_apply hT, Measure.finsetSum_apply, Measure.finsetSum_apply]
    simp only [Measure.restrict_apply hT]
  have hint : IntegrableOn f S ν ↔ ∀ a, IntegrableOn (fun z => f (s a z)) (s a ⁻¹' S) (μ a) := by
    rw [IntegrableOn, hres, integrable_finsetSum_measure]
    simp only [Finset.mem_univ, forall_const]
    exact forall_congr' fun a => (hs a).integrableOn_map_iff
  refine ⟨hint, fun hf => ?_⟩
  have hf' : ∀ a ∈ Finset.univ, Integrable f ((Measure.map (s a) (μ a)).restrict S) := fun a _ =>
    (hs a).integrableOn_map_iff.mpr (hint.mp hf a)
  rw [finsum_eq_sum_of_fintype, hres, integral_finsetSum_measure hf']
  exact Finset.sum_congr rfl fun a _ => (hs a).setIntegral_map _ _

end GlobalTheory.CompanionTheory.Metric
