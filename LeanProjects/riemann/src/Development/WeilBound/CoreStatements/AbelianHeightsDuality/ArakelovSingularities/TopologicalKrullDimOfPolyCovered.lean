import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyDef
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyCons
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyPb
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

theorem polyCovered_pSpace [IsDomain k] (N : ℕ) : PolyCovered (PSpace.str k N) N :=
  polyCovered_pSpace' N

theorem polyCovered_pullback [IsDomain k] {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (a b : ℕ) (hf : PolyCovered f a)
    (hg : PolyCovered g b) : PolyCovered (pullback.fst f g ≫ f) (a + b) :=
  polyCovered_pullback' f g a b hf hg

theorem isIntegral_of_polyCovered [IsDomain k] {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) :
    IsIntegral X :=
  isIntegral_of_polyCovered' f d h

theorem topologicalKrullDim_of_polyCovered [IsDomain k] [IsNoetherianRing k] (hk : ringKrullDim k = 1)
    {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) : topologicalKrullDim X = (d + 1 : ℕ) :=
  topologicalKrullDim_of_polyCovered' hk f d h

theorem ringKrullDim_eq_one [IsDomain k] [CharZero k] (hf : Module.Finite ℤ k) : ringKrullDim k = 1 :=
  ringKrullDim_eq_one' hf

end GlobalTheory.Amb
