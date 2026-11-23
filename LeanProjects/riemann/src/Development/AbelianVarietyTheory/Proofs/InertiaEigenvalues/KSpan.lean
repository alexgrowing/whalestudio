import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.MSpanDecay

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def kSpan : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (G : GA E a → ℂ), GlobalTheory.JSW.IsRapidInf ν k γ ∧ Good G ∧
      F = fun g => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν}

end GlobalTheory.MSpanDecay
