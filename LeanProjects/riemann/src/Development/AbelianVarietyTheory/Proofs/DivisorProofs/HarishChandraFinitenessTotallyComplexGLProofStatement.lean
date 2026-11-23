import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessTotallyComplexGLProof
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
theorem _root_.GlobalTheory.T.harishChandraFinitenessTotallyComplexGL_proof : GlobalTheory.HCF.CoreFiniteGL := by
  first | exact @GlobalTheory.HCFGL.coreFiniteGL | exact GlobalTheory.HCFGL.coreFiniteGL | (intros; apply GlobalTheory.HCFGL.coreFiniteGL <;> assumption) | exact @GlobalTheory.HCFGL.finiteDimensional_single | exact GlobalTheory.HCFGL.finiteDimensional_single | (intros; apply GlobalTheory.HCFGL.finiteDimensional_single <;> assumption)
