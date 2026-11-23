import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramedPointRestrictCoefficientField
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFramedPoint_restrict_coefficient_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (c' : Coeff l) (hle : c.F ≤ c'.F) (T : CDVR) (io' : c'.F →+* T.Fr) (y' : IntFr Xo c' T io'), y'.IsAlg → ∃ y : IntFr Xo c T (io'.comp (IntermediateField.inclusion hle).toRingHom), y.IsAlg ∧ (∀ φ : ℝ, HasPhi y' φ → HasPhi y φ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evI y' (GlobalTheory.FieldBC.rulBC hle f) = evI y f := by
  first | exact @GlobalTheory.RefSum.intFr_res_down | exact GlobalTheory.RefSum.intFr_res_down | (intros; apply GlobalTheory.RefSum.intFr_res_down <;> assumption)
