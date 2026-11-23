import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_cusp_forms_hermitianSpaceSignTwist : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D) (φ : GA D V → ℂ), (IsAutFunSm θ (sgn ε V) (fun g => φ (ofSgn ε V g)) ↔ IsAutFunSm θ V φ) ∧ (IsCuspFun (sgn ε V) (fun g => φ (ofSgn ε V g)) ↔ IsCuspFun V φ) := by
  first | exact @GlobalTheory.sgn_fun_cusp | exact GlobalTheory.sgn_fun_cusp | (intros; apply GlobalTheory.sgn_fun_cusp <;> assumption)
