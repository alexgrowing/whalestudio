import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GmHomAt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

attribute [local instance] Over.cartesianMonoidalCategory

def PhOneValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
    ∀ (m : ℕ) (u0 u1 u2 : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
      (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J →
      ∃ w : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
        (w : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (atP ![φa c φ u0, φa c φ u1, φa c φ u2] C.B.ph1) ∧
        val (ExpGC.cubAt (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2)) (xExp y C φ m).left z J =
          gm (𝟙 _) z ⊤ (unitΓ w) * (val (C.e m) (ptm C ![φa c φ (u0 + u1), φa c φ u2] m).left z J *
            (val (C.e m) (ptm C ![φa c φ u0, φa c φ u2] m).left z J)⁻¹ *
            (val (C.e m) (ptm C ![φa c φ u1, φa c φ u2] m).left z J)⁻¹)

def PhTwoValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
    ∀ (m : ℕ) (u0 u1 u2 : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
      (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J →
      ∃ w : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
        (w : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (atP ![φa c φ u0, φa c φ u1, φa c φ u2] C.B.ph2) ∧
        val (ExpGC.cubAt (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2) (Xo.univ.t.act.act u0)) (xExp y C φ m).left z J =
          gm (𝟙 _) z ⊤ (unitΓ w) * (val (C.e m) (ptm C ![φa c φ u0, φa c φ (u1 + u2)] m).left z J *
            (val (C.e m) (ptm C ![φa c φ u0, φa c φ u1] m).left z J)⁻¹ *
            (val (C.e m) (ptm C ![φa c φ u0, φa c φ u2] m).left z J)⁻¹)

def AdValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
    (∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) →
    ∀ (a' : 𝓞 E) (wL : ExpGC.AdTy Xo a'), ExpGD.AdRel C a' wL →
    ∀ (m : ℕ) (u0 u1 : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
      (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J →
      ∃ w : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
        (w : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (atP ![φa c φ u0, φa c φ u1] (C.B.ad a')) ∧
        val (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1)).left)
            (xExp y C φ m).left z J =
          gm (𝟙 _) z ⊤ (unitΓ w) * (val (C.e m) (ptm C ![φa c φ u0, φa c φ (H.bar a' * u1)] m).left z J *
            (val (C.e m) (ptm C ![φa c φ (a' * u0), φa c φ u1] m).left z J)⁻¹)

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
