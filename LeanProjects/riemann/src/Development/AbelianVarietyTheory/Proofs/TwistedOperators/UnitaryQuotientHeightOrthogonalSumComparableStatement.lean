import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h, quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a := by
  first | exact @GlobalTheory.HtOrth.quotHeight_orthDec_cmp | exact GlobalTheory.HtOrth.quotHeight_orthDec_cmp | (intros; apply GlobalTheory.HtOrth.quotHeight_orthDec_cmp <;> assumption)
