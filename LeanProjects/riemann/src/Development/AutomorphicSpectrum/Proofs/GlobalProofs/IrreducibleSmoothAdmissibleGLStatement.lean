import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_smooth_admissible_GL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.IrreducibleAdmissible k := by
  first | exact @GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible | exact GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible | (intros; apply GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible <;> assumption)
