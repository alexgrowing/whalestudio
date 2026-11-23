import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFramedPoint_baseChange_cdvr_transitive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e : ℕ), 0 < e → (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) → (∃ y' : IntFr Xo c T' (iT.comp io), IsExt y iT e y') ∧ ∀ y' : IntFr Xo c T' (iT.comp io), IsExt y iT e y' → xOf y' = spMap iT ≫ xOf y ∧ ∀ (T'' : CDVR) (iT' : T'.Fr →+* T''.Fr) (e' : ℕ) (y'' : IntFr Xo c T'' (iT'.comp (iT.comp io))), IsExt y' iT' e' y'' → IsExt y (iT'.comp iT) (e' * e) y'' := by
  first | exact @GlobalTheory.PlaceInt.exists_isExt_and_trans | exact GlobalTheory.PlaceInt.exists_isExt_and_trans | (intros; apply GlobalTheory.PlaceInt.exists_isExt_and_trans <;> assumption)
