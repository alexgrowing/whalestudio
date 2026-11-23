import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem unGrp_compactSpace (N : ℕ) : CompactSpace (UNgrp N) :=
  cmpt_compact (ε := fun _ : Fin N => true) fun _ _ => rfl

theorem unGrp_haarProb_exists (N : ℕ) :
    ∃ μ : Measure (UNgrp N), μ.IsHaarMeasure ∧ IsProbabilityMeasure μ := by
  have := unGrp_compactSpace N
  let K : TopologicalSpace.PositiveCompacts (UNgrp N) := ⊤
  refine ⟨Measure.haarMeasure K, inferInstance, ⟨?_⟩⟩
  have h := Measure.haarMeasure_self (K₀ := K)
  simpa [K] using h

end ReciprocityTheory.ChartRestriction.DS
