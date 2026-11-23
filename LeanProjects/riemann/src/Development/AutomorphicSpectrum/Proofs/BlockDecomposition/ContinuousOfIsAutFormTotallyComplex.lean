import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous

open NumberField

namespace GlobalTheory.CompanionTheory.ContAutForm

open GlobalTheory.CuspRep

theorem continuous_of_isAutForm_totallyComplex (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)
    (φ : Sm E N) (h : IsAutForm φ) : Continuous φ.1 :=
  h.continuous

end GlobalTheory.CompanionTheory.ContAutForm
