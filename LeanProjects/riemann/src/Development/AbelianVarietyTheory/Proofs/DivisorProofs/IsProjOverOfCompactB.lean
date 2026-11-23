import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelIsProperOfCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsQProjOverOfIsProper
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem Model.isProjOver_of_compactB (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (_hN : 3 ≤ N) (_hNp : N.Coprime p)
    (hD : D.CompactB) (M : Model b N) : IsProjOver M.s :=
  GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper R M.X M.s M.qproj
    (GlobalTheory.T.harrisTaylor_integralModel_isProper_of_compact p D R b N M hD)

end GlobalTheory.UPel.HT
