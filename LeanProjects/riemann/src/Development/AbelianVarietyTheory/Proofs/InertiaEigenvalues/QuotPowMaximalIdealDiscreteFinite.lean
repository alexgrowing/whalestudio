import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem quot_pow_maximalIdeal_discrete_finite :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ,
      DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  intro p O _ _ _ _ _ hO k
  haveI : CompactSpace O := hO.compact
  set I : Ideal O := IsLocalRing.maximalIdeal O ^ k with hI
  have hopen : IsOpen ((I : Ideal O) : Set O) := (isAdic_iff.mp hO.adic).1 k
  have hdisc : DiscreteTopology (O ⧸ I) := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have himg : (Ideal.Quotient.mk I) '' (I : Set O) = {0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hx
      · rintro rfl
        exact ⟨0, I.zero_mem, map_zero _⟩
    rw [← himg]
    exact QuotientRing.isOpenMap_coe I _ hopen
  refine ⟨hdisc, ?_⟩
  haveI : CompactSpace (O ⧸ I) := Quotient.compactSpace
  exact finite_of_compact_of_discrete

end GlobalTheory.NatQuot
