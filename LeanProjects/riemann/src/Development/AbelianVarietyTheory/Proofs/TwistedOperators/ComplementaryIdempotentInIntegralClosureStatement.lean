import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdempotentInIntegralClosure
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementary_idempotent_in_integral_closure : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → finPart D (1 - cA D e) ∈ AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, x ∈ GlobalTheory.LiftLevel.liftI Pg Q ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)} := by
  first | exact @GlobalTheory.ConjCompl.offConj | exact GlobalTheory.ConjCompl.offConj | (intros; apply GlobalTheory.ConjCompl.offConj <;> assumption)
