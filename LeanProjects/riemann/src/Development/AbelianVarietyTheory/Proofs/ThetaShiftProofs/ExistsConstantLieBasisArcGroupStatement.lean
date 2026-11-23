import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constantLieBasis_arcGroup : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ), ∃ (g : ℕ) (e : Fin g → Out.GtPt a.D₀ (epsR A)) (v : Fin g → (epsR (PowerSeries A) ⟶ W.t.G)) (M : 𝓞 E → Matrix (Fin g) (Fin g) A), (∀ i, GtTanR (e i) ∧ LieImg W (e i) (v i)) ∧ IsLieBasis v ∧ (∀ ν, GtTanR ν → ∃! cf : Fin g → A, GtComb cf e ν) ∧ ∀ (x : 𝓞 E) i, IsLieComb (fun k => PowerSeries.C (R := A) (M x i k)) v (v i ≫ W.t.act.act x) := by
  first | exact @GlobalTheory.ConstLie.exists_const_basis | exact GlobalTheory.ConstLie.exists_const_basis | (intros; apply GlobalTheory.ConstLie.exists_const_basis <;> assumption)
