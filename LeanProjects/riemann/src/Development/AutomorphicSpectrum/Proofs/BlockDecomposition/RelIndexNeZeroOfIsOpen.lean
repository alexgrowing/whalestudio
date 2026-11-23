import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
open GlobalTheory.BCT GlobalTheory.CompanionTheory.SplitConvTw
open scoped Classical Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitConvHecke

theorem relIndex_ne_zero_of_isOpen {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (K L : Subgroup H) (hL : IsOpen (L : Set H)) (hK : IsCompact (K : Set H)) :
    L.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hop : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) :=
    hL.preimage continuous_subtype_val
  haveI : Finite (K ⧸ L.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hop
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.SplitConvHecke
