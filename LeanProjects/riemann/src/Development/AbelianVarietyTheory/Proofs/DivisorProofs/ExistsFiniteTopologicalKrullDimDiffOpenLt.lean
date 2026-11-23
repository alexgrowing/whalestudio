import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.Div

theorem exists_finite_topologicalKrullDim_diff_lt :
    ∀ (T : Type) [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] [T0Space T] (Z : Set T),
      IsClosed Z → ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → ∀ d : ℕ,
        (topologicalKrullDim Z < (d + 1 : ℕ) → topologicalKrullDim (Z \ U : Set T) < (d : ℕ)) := by
  intro T _ _ _ _ Z _
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  have hne : ∀ K : irreducibleComponents Z, ∃ x : Z, x ∈ (K : Set Z) := fun K => K.2.1.nonempty
  choose p hp using hne
  haveI : Finite (irreducibleComponents Z) := hfin.to_subtype
  refine ⟨Set.range (fun K => (p K : T)), Set.finite_range _, fun U _ hSU d hd => ?_⟩
  have hsub : (Z \ U : Set T) ⊆ Z := Set.diff_subset
  have hi : IsInducing (Set.inclusion hsub) := (IsEmbedding.inclusion hsub).isInducing
  have hcl : IsClosed {x : Z | (x : T) ∉ U} :=
    (IsOpen.preimage continuous_subtype_val ‹IsOpen U›).isClosed_compl
  refine Order.krullDim_lt_coe_iff.2 fun s => ?_
  have hm := IrreducibleCloseds.map_strictMono_of_isInducing hi
  let s' := s.map _ hm
  obtain ⟨K, hK, hsK⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (s'.last : Set Z) s'.last.isIrreducible
  let K' : IrreducibleCloseds Z := ⟨K, hK.1, isClosed_of_mem_irreducibleComponents K hK⟩
  have hlast : (s'.last : Set Z) ⊆ {x : Z | (x : T) ∉ U} := by
    have : s'.last = IrreducibleCloseds.map _ hi.continuous s.last := by
      simp [s']
    rw [this]
    refine closure_minimal ?_ hcl
    rintro _ ⟨y, -, rfl⟩
    exact y.2.2
  have hlt : s'.last < K' := by
    refine lt_of_le_of_ne hsK fun h => ?_
    have h1 : p ⟨K, hK⟩ ∈ (s'.last : Set Z) := by
      rw [h]; exact hp ⟨K, hK⟩
    exact hlast h1 (hSU ⟨⟨K, hK⟩, rfl⟩)
  have h2 := Order.krullDim_lt_coe_iff.1 hd (s'.snoc K' hlt)
  simp [s'] at h2
  exact h2

end GlobalTheory.Div
