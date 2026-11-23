import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem relIndex_ne_zero_of_isOpen_le_isCompact {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (K U : Subgroup H) (hK : IsCompact (K : Set H))
    (hU : IsOpen (U : Set H)) (_hUK : U ≤ K) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hO : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) :=
    hU.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hO
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory
