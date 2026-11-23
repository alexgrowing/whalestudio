import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameChange_exists_unique_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y : FrPt Xo c S), ((∀ τ, IsUnit (g τ).det) → IsUnit s → ∃ y', FrChg g s y y') ∧ (∀ y' y'', FrChg g s y y' → FrChg g s y y'' → y' = y'') ∧ (∀ y', FrChg g s y y' → (∀ τ, IsUnit (g τ).det) ∧ IsUnit s) ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃ (g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s' : S), FrChg g' s' y y' := by
  first | exact @GlobalTheory.ArcQ.frChg_exists_unique_units | exact GlobalTheory.ArcQ.frChg_exists_unique_units | (intros; apply GlobalTheory.ArcQ.frChg_exists_unique_units <;> assumption)
