import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ruleBaseChange_section_values_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, rulBC hle f ∈ sec Xo c' a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S), evR Xo c' (rulBC hle f) y = evR Xo c f (y.res hle h)) ∧ (∀ (t : c.F) (f g : Rul Xo c), rulBC hle (t • f + g) = incF c c' hle t • rulBC hle f + rulBC hle g) := by
  first | exact @GlobalTheory.FieldBC.rulBC_sec_val_linear | exact GlobalTheory.FieldBC.rulBC_sec_val_linear | (intros; apply GlobalTheory.FieldBC.rulBC_sec_val_linear <;> assumption)
