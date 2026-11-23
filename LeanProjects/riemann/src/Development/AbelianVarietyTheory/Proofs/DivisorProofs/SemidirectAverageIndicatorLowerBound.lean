import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularAndLintegralUnfoldOfLattice
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal Pointwise

namespace GlobalTheory.ResLine.LowerAverage

theorem countable_subgroupOf {G : Type} [Group G] (Λ N : Subgroup G) [Countable Λ] :
    Countable (Λ.subgroupOf N) := by
  refine Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : Λ)) ?_
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : Λ => (z : G)) h))

theorem right_of_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (N Λ : Subgroup G) [Countable Λ] (hN : IsClosed (N : Set G)) (ν : Measure N)
    (hν : ν.IsHaarMeasure) (D : Set N) (hD : IsFundamentalDomain (Λ.subgroupOf N) D ν)
    (hfin : ν D ≠ ⊤) : ν.IsMulRightInvariant := by
  haveI : BorelSpace N := Subtype.borelSpace (N : Set G)
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := countable_subgroupOf Λ N
  exact RightUnfold.isMulRightInvariant_of_lattice ν (Λ.subgroupOf N) D hD hfin

theorem average_lower : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ C : Set G, IsCompact C → ∃ (U : Set G) (c : ℝ≥0∞), IsOpen U ∧ μ U ≠ ⊤ ∧ c ≠ 0 ∧ ∀ u₀ ∈ N, ∀ m₀ ∈ M, ∀ y ∈ C, c ≤ ∫⁻ m : M, ∫⁻ u : N, U.indicator 1 ((u : G) * m * (u₀ * m₀ * y)) ∂ν ∂π := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM H μ hμ C hC
  haveI : BorelSpace N := Subtype.borelSpace (N : Set G)
  haveI : BorelSpace M := Subtype.borelSpace (M : Set G)
  haveI := H.haarN
  haveI := H.haarM
  haveI := right_of_closed N Λ H.closedN ν H.haarN DN H.domN H.finN
  haveI := right_of_closed M Λ H.closedM π H.haarM DM H.domM H.finM
  obtain ⟨K, hK, hCK⟩ := exists_compact_superset hC
  obtain ⟨W, hW, hWC⟩ := compact_open_separated_mul_left hC isOpen_interior hCK
  obtain ⟨V, hVo, hV1, hVW⟩ := exists_open_nhds_one_mul_subset hW
  have hVN : IsOpen ((↑) ⁻¹' V : Set N) := hVo.preimage continuous_subtype_val
  have hVM : IsOpen ((↑) ⁻¹' V : Set M) := hVo.preimage continuous_subtype_val
  refine ⟨interior K, ν ((↑) ⁻¹' V) * π ((↑) ⁻¹' V), isOpen_interior,
    ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne,
    mul_ne_zero (hVN.measure_ne_zero ν ⟨1, hV1⟩) (hVM.measure_ne_zero π ⟨1, hV1⟩), ?_⟩
  intro u₀ hu₀ m₀ hm₀ y hy
  have h1 : ∀ m : M, ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞) ((u : G) * m * (u₀ * m₀ * y)) ∂ν
      = ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * ((m * ⟨m₀, hm₀⟩ : M) : G) * y) ∂ν := by
    intro m
    rw [← lintegral_mul_right_eq_self (fun u : N => (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * ((m * ⟨m₀, hm₀⟩ : M) : G) * y)) ⟨m * u₀ * (m : G)⁻¹, H.norm m m.2 u₀ hu₀⟩]
    refine lintegral_congr fun u => ?_
    congr 1
    simp only [Subgroup.coe_mul]
    group
  simp_rw [h1]
  rw [lintegral_mul_right_eq_self (fun m : M => ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * (m : G) * y) ∂ν) ⟨m₀, hm₀⟩, ← lintegral_indicator_const hVM.measurableSet]
  refine lintegral_mono fun m => ?_
  by_cases hm : m ∈ ((↑) ⁻¹' V : Set M)
  swap
  · rw [Set.indicator_of_notMem hm]
    exact bot_le
  rw [Set.indicator_of_mem hm]
  rw [← lintegral_indicator_one hVN.measurableSet]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ ((↑) ⁻¹' V : Set N)
  swap
  · rw [Set.indicator_of_notMem hu]
    exact bot_le
  rw [Set.indicator_of_mem hu]
  have : (u : G) * m * y ∈ interior K :=
    hWC (Set.mul_mem_mul (hVW (Set.mul_mem_mul hu hm)) hy)
  rw [Set.indicator_of_mem this]
  exact le_rfl

end GlobalTheory.ResLine.LowerAverage
