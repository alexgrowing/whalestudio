import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvrPf

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ModelSquareFunctions

theorem isProper_genericFibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    {y : letI := io.toAlgebra; FrPt Xo c T.Fr} (I : IntData Xo c T io y) :
    IsProper ((Over.pullback (spMap (algebraMap T.V (FractionRing T.V)))).obj I.G.G).hom := by
  have h1 := I.m1.cart.1
  have h2 := I.m2.cart.1
  have hp : IsProper I.t'.G.hom := MorphismProperty.of_isPullback h1 Xo.univ.proper
  show IsProper (pullback.snd I.G.G.hom (spMap (algebraMap T.V (FractionRing T.V))))
  rw [← h2.isoPullback_inv_snd]
  infer_instance

theorem surjective_appTop_square : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y), Function.Surjective (I.G.G ⊗ I.G.G).hom.appTop.hom := by
  intro E _ _ _ H Dw l Xo c T io y I
  have h := (globalFnsDvr_of_globalFns GlobalTheory.globalFns_holds E H T.V T.cpl I.G (isProper_genericFibre I) 2).2
  let e : powObj I.G.G 2 ≅ I.G.G ⊗ I.G.G := I.G.G ◁ᵢ (ρ_ I.G.G)
  have hw : e.inv.left ≫ (powObj I.G.G 2).hom = (I.G.G ⊗ I.G.G).hom := Over.w e.inv
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : IsIso e.inv.left.appTop := inferInstanceAs (IsIso (e.inv.left.app ⊤))
  rw [← hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso e.inv.left.appTop).2.comp h

end GlobalTheory.ModelSquareFunctions
