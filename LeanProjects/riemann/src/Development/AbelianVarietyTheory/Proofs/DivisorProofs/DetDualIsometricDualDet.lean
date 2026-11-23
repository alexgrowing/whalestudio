import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDualMetricIsometric
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem HermVB.isometric_det_dual :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (r : ℕ) (E : HermVB p r),
      E.dual.det.Isometric E.det.dual :=
  fun k _ X p r E => VMetric.isometric_det_dual k X p E.E r E.h E.cInf

end GlobalTheory
