import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem extPt (Y : Model Xo c β) (T : CDVR) (b : O →+* T.V) (x : Sp T.Fr ⟶ Xo.XF c)
    (hx : x ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b) :
    ∃ yt : Sp T.V ⟶ Y.X, Out.jK T.V ≫ yt = x ≫ Y.j ∧ yt ≫ Y.s = spMap b := by
  haveI : IsProper Y.s := projProper _ _ _ Y.proj
  have hE : ValuativeCriterion.Existence Y.s := by
    have h1 : UniversallyClosed Y.s := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h1
    exact h1.1
  let S : ValuativeCommSq Y.s :=
    { R := T.V, K := FractionRing T.V, i₁ := x ≫ Y.j, i₂ := spMap b,
      commSq := ⟨by rw [Category.assoc]; exact hx⟩ }
  obtain ⟨⟨⟨l, hl1, hl2⟩⟩⟩ := hE S
  exact ⟨l, hl1, hl2⟩

end Formalism.L2.Pj
