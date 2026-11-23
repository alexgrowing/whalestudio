import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfProperSpecialFibreUniversallyOpenDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodRedProper

theorem isProper_of_proper_fibres :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → IsProper (GlobalTheory.SS.spFibre G).hom → IsProper G.hom := by
  intro W L _ _ _ _ _ _ G _ h _ h2
  obtain ⟨a, b, c, d, e⟩ := h
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  exact GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr W G.left G.hom inferInstance inferInstance inferInstance inferInstance inferInstance h2

end GlobalTheory.GoodRedProper
