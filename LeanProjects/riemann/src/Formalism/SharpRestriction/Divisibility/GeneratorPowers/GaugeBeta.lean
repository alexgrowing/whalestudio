import Formalism.LocalToGlobal.ProjectiveLattices.IsExpChart
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def BetaUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (a : 𝓞 E) (β β' : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε)),
    β.IsGen → β'.IsGen →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β' (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    β = β'

namespace GaugeBeta

theorem pull_unit_eq_one_k {X Y S0 : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : S0 ⟶ Y) (ψ : S0 ⟶ X) (k : ℤ)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => k))
    (t t' : LB.Gen (LB.LinComb L φ ε)) (u : Γ(Y, ⊤)ˣ)
    (hu : ∀ j, t.s j = res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) u * t'.s j)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) rig)
    (hc' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' h) rig) :
    (h.app ⊤).hom (u : Γ(Y, ⊤)) = 1 := by

  let rig1 : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1) := ⟨rig.s⟩
  exact pull_unit_eq_one L hL φ ε h ψ rig1 t t' u hu hc hc'

end GaugeBeta

theorem betaUniq_of_global (hglob : GlobalFnsSt) : BetaUniqSt := by
  intro E _ _ _ H Dw l Xo a β β' hβ hβ' hc hc'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨u, hu⟩ := gen_ratio _ (wchart_cover Xo.univ.t.PP.L hL _) β β' hβ hβ'
  have h1 := GaugeBeta.pull_unit_eq_one_k Xo.univ.t.PP.L hL _ _ (eSec Xo.univ.t.G)
    (eSec Xo.univ.t.G) (-3) (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) β β' u hu hc hc'
  have hu1 : u = 1 := by
    obtain ⟨v, hv⟩ := (hglob _ Xo.univ.t.G (isAbelianScheme_univ Xo)).2 (u : Γ(Xo.univ.t.G.left, ⊤))
    have hw : eSec Xo.univ.t.G ≫ Xo.univ.t.G.hom = 𝟙 _ := by
      unfold eSec
      exact Over.w _
    have e1 : (Scheme.Hom.app (eSec Xo.univ.t.G) ⊤).hom
        ((Scheme.Hom.appTop Xo.univ.t.G.hom).hom v) = v := by
      have := congrArg (fun f => (Scheme.Hom.appTop f).hom v) hw
      simp at this
      exact this
    rw [hv] at e1
    have hv1 : v = 1 := e1.symm.trans h1
    apply Units.ext
    rw [← hv, hv1, map_one]
    rfl
  cases β
  cases β'
  congr 1
  funext j
  have hj := hu j
  rw [hu1, map_one, one_mul] at hj
  exact hj

end Formalism.MainNotions.ModuliIntegralCharts.H1
