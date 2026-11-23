import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def IntChartStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V →
    ∀ (t : SAB H (Sp V)),
    IsProper ((Over.pullback (spMap (algebraMap V (FractionRing V)))).obj t.G).hom →
    ∀ {κ : Type} [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)),
      (∀ ℓ, IsTanAtG t (𝟙 (Sp V)) (tg ℓ)) →
      (∀ w, IsTanAtG t (𝟙 (Sp V)) w →
        ∃! a : κ → V, IsCombAtG t (𝟙 (Sp V)) (m := Fintype.card κ)
          (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) →
      ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
      ∃ (d : ℕ) (B : Germ.FB V d (𝓞 E)) (uvec : κ → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
        (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t),
        d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧
        IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uvec x ∧
        IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e ∧
        IsPrimG t wP ∧ FrTrunc t (𝟙 (Sp V)) d x e ∧ Rig0G t (𝟙 (Sp V)) d x B.A.act e wP ∧
        ∀ (k : ℕ) (F : LB.Sec (LPow t.G t.PP.L k (Over.mk (𝟙 (Sp V))))),
          ∃ f, IsGermG t (𝟙 (Sp V)) d x B.A.act e wP k F f

end Formalism.MainNotions.ModuliIntegralCharts.H1
