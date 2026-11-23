import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ClosedSubgroupsStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSFA

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS.Mult1

theorem haarUniq2 : HaarUniq2Statement := by
  intro k r U μ ν hU hμ hν
  haveI : Fact (Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hμs, hμ0, hμc, hμl⟩ := hμ
  obtain ⟨hνs, hν0, hνc, hνl⟩ := hν
  have hμc' : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hμc
  have hνc' : ν (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hνc
  haveI := hμs
  haveI := hνs
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) ν
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap μ hμc' hμl
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap ν hνc' hνl
  have hμ0' : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hμ0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val μ hμc', h, Measure.map_zero]
  have hν0' : ν.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hν0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', h, Measure.map_zero]
  obtain ⟨c, hc, hcE⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hν0' hμ0'
  refine ⟨c, pos_iff_ne_zero.mpr hc, ?_⟩
  rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', hcE, Measure.map_smul, HaarSigmaFiniteUniqueness.map_comap_val μ hμc']

end ReciprocityTheory.ChartRestriction.DS.Lap
