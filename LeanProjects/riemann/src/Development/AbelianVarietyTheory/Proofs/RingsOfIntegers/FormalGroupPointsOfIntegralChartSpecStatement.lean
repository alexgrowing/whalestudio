import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpec
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_group_points_of_integral_chart_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → (FormPt C 1 0) ∧ (∀ (a a' : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (al al' : Fin (chD C.ch) → T.V), FormPt C a al → FormPt C a' al' → (a = a' ↔ al = al')) ∧ (∀ (a a' : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (al al' δ : Fin (chD C.ch) → T.V), FormPt C a al → FormPt C a' al' → (cpt δ : Pt T.V 0 (chD C.ch)) = addV B.G.F (cpt al) (cpt al') → FormPt C (a * a') δ) ∧ (∀ (a : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (al δ : Fin (chD C.ch) → T.V) (o : 𝓞 E), FormPt C a al → (cpt δ : Pt T.V 0 (chD C.ch)) = compV (B.A.act o) (cpt al) → FormPt C (a ≫ Xo.univ.t.act.act o) δ) ∧ ∀ al : Fin (chD C.ch) → T.V, Small al → ∃ a : (ptO Xo (xOf y) ⟶ Xo.univ.t.G), FormPt C a al := by
  first | exact @GlobalTheory.PlaceFormPt.formPt_spec | exact GlobalTheory.PlaceFormPt.formPt_spec | (intros; apply GlobalTheory.PlaceFormPt.formPt_spec <;> assumption)
