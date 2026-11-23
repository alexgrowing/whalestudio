import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_module_finite_length : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  first | exact @GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | (intros; apply GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength <;> assumption)
