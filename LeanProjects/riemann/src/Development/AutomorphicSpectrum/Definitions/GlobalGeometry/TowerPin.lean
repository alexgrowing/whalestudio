import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlCTendsto
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH

def TowerPin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (a : WZ E) (B : ℕ) (top dg : Comp Xo c → ℚ → ℝ) : Prop :=
  ∃ (_ : DecidableEq (CMType H)) (II : IntersectionSystem) (Xf : ∀ l : Level H, Moduli Dw l) (hX : Xo = Xf l)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T)
    (κ : Comp Xo c ≃ T.Comp), IsFullIntersectionSystem II ∧ Top.IsGlobal Xf l c (hX ▸ Y) ∧ o.Extra ∧
      CompOf o.toTowerOrigin κ ∧ ∀ (Z : Comp Xo c) (s : ℚ),
        top Z s = T.mbarTop II B (κ Z) (towerWt Dw a) s ∧ dg Z s = T.mDeg B (κ Z) (towerWt Dw a) s

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def MbarPin {D : D7} {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) (up : RW D) (g : ℝ) (Bm : MbarIn S i up) :
    Prop :=
  TowerPin (S.Xo i) S.c (wtZ' D i up) ⌊Top.bigB0 (towerWt (Q.Dw ((i : ℕ) + 1)) (wtZ' D i up)) g⌋₊ Bm.top Bm.dg

end GlobalTheory.CompanionTheory.Ar.Rec
