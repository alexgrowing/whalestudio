import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} := by
  first | exact @GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi | exact GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi | (intros; apply GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi <;> assumption)
