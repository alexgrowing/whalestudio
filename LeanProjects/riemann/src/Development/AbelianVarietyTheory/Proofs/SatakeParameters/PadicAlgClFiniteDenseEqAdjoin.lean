import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem GlobalTheory.padicAlgCl_finite_dense_eq_adjoin : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)), (∀ x, c x ∈ K) → FiniteDimensional ℚ_[l] K → (K : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → K = IntermediateField.adjoin ℚ_[l] (Set.range c) := by
  intro l _ E _ _ c K hc hfin hdense
  have hle : IntermediateField.adjoin ℚ_[l] (Set.range c) ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩; exact hc x
  have hKfin : FiniteDimensional ℚ_[l] K.toSubalgebra.toSubmodule := hfin
  have hAfin : FiniteDimensional ℚ_[l]
      (IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule :=
    Submodule.finiteDimensional_of_le (S₂ := K.toSubalgebra.toSubmodule) hle
  have hclosed : IsClosed ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule
      : Set (PadicAlgCl l)) :=
    Submodule.closed_of_finiteDimensional _
  apply le_antisymm _ hle
  intro y hy
  have h1 : closure (Set.range c) ⊆
      ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule : Set (PadicAlgCl l)) := by
    apply closure_minimal _ hclosed
    rintro _ ⟨x, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  exact h1 (hdense hy)
