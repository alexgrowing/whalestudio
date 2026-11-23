import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), Function.Bijective C.toH ∧ ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsFock B (C.Th (C.xB B) φ) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B (C.Th (C.xB B) φ) Q 0 = thP C.X C.hr C.bas C.idx φ (C.toH Q) (C.xB B) := by
  first | exact @GlobalTheory.Ker.fvec_Th_zero | exact GlobalTheory.Ker.fvec_Th_zero | (intros; apply GlobalTheory.Ker.fvec_Th_zero <;> assumption)
