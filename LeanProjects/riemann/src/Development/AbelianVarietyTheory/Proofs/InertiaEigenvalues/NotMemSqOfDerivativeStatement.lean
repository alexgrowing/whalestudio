import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivative
import Mathlib
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraMap_not_mem_sq_of_derivative_not_mem : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (p : HeightOneSpectrum (𝓞 E)) (P : HeightOneSpectrum (𝓞 E')) (β : 𝓞 E') (f : Polynomial ℤ),
    f.Monic → Polynomial.aeval β f = 0 → Algebra.adjoin E {(β : E')} = ⊤ →
    (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 E') x ∈ P.asIdeal ↔ x ∈ p.asIdeal) →
    Polynomial.aeval β (Polynomial.derivative f) ∉ P.asIdeal →
    ∀ c : 𝓞 E, c ∉ p.asIdeal ^ 2 → algebraMap (𝓞 E) (𝓞 E') c ∉ P.asIdeal ^ 2 := by
  first | exact @GlobalTheory.UnramSimpleGen.not_mem_sq_of_derivative | exact GlobalTheory.UnramSimpleGen.not_mem_sq_of_derivative | (intros; apply GlobalTheory.UnramSimpleGen.not_mem_sq_of_derivative <;> assumption)
