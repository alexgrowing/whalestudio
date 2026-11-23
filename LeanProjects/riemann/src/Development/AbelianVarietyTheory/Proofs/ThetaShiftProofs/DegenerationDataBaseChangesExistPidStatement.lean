import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_baseChanges_exist_pid : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A A' : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing A'] [IsDomain A'] [IsPrincipalIdealRing A'] (b : O →+* A) (a : ArcIn Dw l β A b) (f : A →+* A'), Function.Injective f → ∀ b' : O →+* A', b' = f.comp b → (∃ (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀), InBC f a a' p) ∧ ∀ (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀), InBC f a a' p → (∀ (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ), ∃ W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ), WitBC f p W W') ∧ (∀ ν, ∃! ν', LetBC p ν ν') ∧ (∀ ν ν', LetBC p ν ν' → GtTanR ν → GtTanR ν') ∧ (∀ th, ∃! th', ThBC p th th') ∧ ∀ th th', ThBC p th th' → ThNZ th → ThNZ th' := by
  first | exact @GlobalTheory.ArcQBC.baseChanges | exact GlobalTheory.ArcQBC.baseChanges | (intros; apply GlobalTheory.ArcQBC.baseChanges <;> assumption)
