import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.IsPositiveDefiniteForm
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

section Frame

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mass_eq_sum_inv_aut_card (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (s : Finset (Submodule (𝓞 K) V))
    (hs : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    Formalism.HermitianLatticesTheory.mass h L = ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ := by
  have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨s, hs⟩
  rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h L hex]
  apply Complex.ofReal_injective
  rw [Formalism.HermitianLatticesTheory.massBasic_sum_cast, Formalism.HermitianLatticesTheory.massBasic_sum_cast]
  exact Formalism.ThetaLiftIndependence.latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs

end Frame

section Rec

variable (D : D7) (large₂ : SizeData₂ D)

end Rec

end Formalism.MainNotions.BridgeLemma₂

end
