import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelCoverLargerCoeffFieldLyingOver
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_larger_coeffField_lying_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (d : DeltaDat Xo c n), (∀ (k : Type) [CommRing k] [Algebra c.F k] [Algebra c'.F k] [Algebra d.c₂.F k] [A₂ : Algebra (covCoeff hle d).F k] (h : AlgOver c c' hle k) (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k) (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (y : FrPt Xo c' k), @FrOver E _ _ _ H Dw l Xo c' n (ddBC hle d) k _ _ A₂ y₂ y ↔ FrOver d (y₂.res (le_covCoeff hle d) h₂) (y.res hle h)) ∧ (d.IsLev → (ddBC hle d).IsLev) := by
  first | exact @GlobalTheory.FieldBC.frOver_isLev_ddBC | exact GlobalTheory.FieldBC.frOver_isLev_ddBC | (intros; apply GlobalTheory.FieldBC.frOver_isLev_ddBC <;> assumption)
