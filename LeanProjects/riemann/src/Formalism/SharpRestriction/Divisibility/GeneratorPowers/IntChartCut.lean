import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)

def ChartDataGSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0)
    (S : Type) [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) {κ : Type} [Fintype κ]
    (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)),
    (∀ ℓ, IsTanAtG t x0 (tg ℓ)) →
    (∀ w, IsTanAtG t x0 w →
      ∃! a : κ → S, IsCombAtG t x0 (m := Fintype.card κ)
        (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) →
    ∃ (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G),
      d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧
      IsChartG t x0 d G.F A.act tg uvec x

end Formalism.MainNotions.ModuliIntegralCharts.H1
