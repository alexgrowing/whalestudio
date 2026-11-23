import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsTranslateUnitSymmetricFormalGroupPoint
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translateUnit_symmetric_formalGroup_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (Θ : PS T.V 3 (chD C.ch)) (jo : PS T.V 1 (chD C.ch)), IsTheta B T.Fr (gaugeOf C) H.w0 Θ → IsIota B T.Fr (gaugeOf C) H.w0 jo → ∀ (k : ℕ), Odd k → ∀ (a : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) α, FormPt C a α → a ^ k = 1 → ∃ u : PS T.V 1 (chD C.ch), TrUnit B Θ jo k α u ∧ ∀ (F F' : SecN Xo (xOf y) k) (f : PS T.V 1 (chD C.ch)), Regular C k F → GermIs C k F f → Moves Xo a F F' → GermIs C k F' (u * shift B.G.F (fun _ => α) f) := by
  first | exact @GlobalTheory.TransUnit.exists_trUnit | exact GlobalTheory.TransUnit.exists_trUnit | (intros; apply GlobalTheory.TransUnit.exists_trUnit <;> assumption)
