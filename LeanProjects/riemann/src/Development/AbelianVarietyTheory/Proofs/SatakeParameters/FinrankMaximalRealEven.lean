import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
open NumberField

namespace GlobalTheory.RealGal

theorem QCM.even_finrank_maximalRealSubfield (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) := by
  have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield Q.K) Q.K
  have h2 := Module.finrank_mul_finrank ℚ E Q.K
  have h3 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield Q.K) Q.K] at h1
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h3
  rw [Q.two] at h2
  exact ⟨Module.finrank ℚ (maximalRealSubfield E), by omega⟩

end GlobalTheory.RealGal
