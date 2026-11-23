import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB

namespace GlobalTheory.Vert.Model

theorem topologicalKrullDim_gen : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O), topologicalKrullDim Z.gen.toScheme = Z.relDim := by
  intro O _ _ _ Z
  obtain ⟨q, H⟩ := Z.exists_isPullback_gen (FractionRing O)
  obtain ⟨d, hd, -⟩ := exists_topologicalKrullDim_fibres_eq_of_isPullback Z.str (FractionRing O)
    (IsLocalRing.ResidueField O) IsLocalRing.residue_surjective (IsPullback.of_hasPullback _ _) H
  rw [hd, relDim_eq_iff.2
    (IntModel.topologicalKrullDim_eq_succ (IsDiscreteValuationRing.not_isField O) H hd)]

end GlobalTheory.Vert.Model
