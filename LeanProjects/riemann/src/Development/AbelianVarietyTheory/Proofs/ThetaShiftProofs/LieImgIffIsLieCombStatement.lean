import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (m : ℕ) (cf : Fin m → A) (e : Fin m → Out.GtPt a.D₀ (epsR A)) (ν : Out.GtPt a.D₀ (epsR A)) (v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)) (w : epsR (PowerSeries A) ⟶ W.t.G), (∀ i, LieImg W (e i) (v i)) → GtComb cf e ν → (LieImg W ν w ↔ IsLieComb (fun i => PowerSeries.C (R := A) (cf i)) v w) := by
  first | exact @GlobalTheory.ConstLin.lieImg_iff_isLieComb | exact GlobalTheory.ConstLin.lieImg_iff_isLieComb | (intros; apply GlobalTheory.ConstLin.lieImg_iff_isLieComb <;> assumption)
