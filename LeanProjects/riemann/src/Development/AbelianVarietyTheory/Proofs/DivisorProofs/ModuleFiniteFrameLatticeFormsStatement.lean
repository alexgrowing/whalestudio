import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFiniteFrameLatticeForms
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_frameLatticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  first | exact @GlobalTheory.ExpFrame.Frame.finite_latticeForms | exact GlobalTheory.ExpFrame.Frame.finite_latticeForms | (intros; apply GlobalTheory.ExpFrame.Frame.finite_latticeForms <;> assumption)
