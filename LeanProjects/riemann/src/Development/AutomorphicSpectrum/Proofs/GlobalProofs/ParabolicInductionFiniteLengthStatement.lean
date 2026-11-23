import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_induction_finite_length : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionFiniteLength k := by
  first | exact @GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength | exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength | (intros; apply GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength <;> assumption)
