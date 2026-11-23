import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.OpenFiniteIndex

theorem compactSpace_fixing (l : ℕ) [Fact l.Prime] (K : FinExt l) : CompactSpace ↥(GK K) := by
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  have hc : IsClosed ((K.1.fixingSubgroup : Subgroup (GQ l)) : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.mp hc.isCompact

theorem finiteIndex_of_isOpen : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (H : Subgroup ↥(GK K)),
    IsOpen (H : Set ↥(GK K)) → H.FiniteIndex := by
  intro l _ K H hH
  haveI := compactSpace_fixing l K
  haveI : Finite (↥(GK K) ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  exact Subgroup.finiteIndex_of_finite_quotient

end GlobalTheory.OpenFiniteIndex
