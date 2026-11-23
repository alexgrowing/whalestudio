import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOf
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_thetaOf_alt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec), ThNZ th → (∃! θ : LB.Sec W.t.PP.L, ThetaOf W th θ) ∧ ∀ θ, ThetaOf W th θ → (∀ s : LB.Sec W.t.PP.L, ∃! r : PowerSeries A, ∀ i, s.f i = constFn W.t.G.hom _ r * θ.f i) ∧ (∃ g : W.t.G.left, W.t.G.hom g = IsLocalRing.closedPoint (PowerSeries A) ∧ g ∈ Out.nonzeroLocus θ) ∧ ∀ (r : A) (th' : a.D₀.P.L.Sec) (θ' : LB.Sec W.t.PP.L), ThMul r th th' → (ThetaOf W th' θ' ↔ ∀ i, θ'.f i = constFn W.t.G.hom _ (PowerSeries.C (R := A) r) * θ.f i) := by
  first | exact @GlobalTheory.existsUnique_thetaOf | exact GlobalTheory.existsUnique_thetaOf | (intros; apply GlobalTheory.existsUnique_thetaOf <;> assumption)
