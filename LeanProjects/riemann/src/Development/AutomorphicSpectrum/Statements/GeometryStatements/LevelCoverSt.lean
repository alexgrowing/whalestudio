import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt

namespace GlobalTheory.CompanionTheory.Ar.XR

open AlgebraicGeometry CategoryTheory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

def LevelCoverSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (e : Y.X), e ∈ genericPoints Y.X →
    ∀ N : ℕ, 1 ≤ N → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (n : ℕ) (x : Fin n → Ω) (M : PModel ℤ x)
      (f : M.X ⟶ Y.X) (y : Sp Ω ⟶ Xo.XF c) (t : SAB H M.X) (_ : SABMap t Y.t f) (z : Ωˣ)
      (ev : D.La → (Over.mk M.ξ ⟶ t.G)),
      Flat.NormalCpt M.ξ ∧ IsFinite f ∧ f (GlobalTheory.CompanionTheory.Ar.genPt M.ξ) = e ∧ M.ξ ≫ f = y ≫ Y.j ∧ IsFullLevelAt D t M.ξ N z ev ∧
      FullTorsion t.G M.ξ N ∧ ∀ q : Cpt M.ξ, unitAt M.ξ q (z : Ω)

end GlobalTheory.CompanionTheory.Ar.XR
