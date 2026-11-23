import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCAlpha

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def lapOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    ((lieS E a i j (atEmb τ 1)) ^ 2 + (lieS E a i j (atEmb τ Complex.I)) ^ 2)

def casKOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (1 / 4 : ℂ) •
    ((lieS E a i j (atEmb τ 1) - lieS E a j i (atEmb τ 1)) ^ 2 +
      (lieS E a i j (atEmb τ Complex.I) + lieS E a j i (atEmb τ Complex.I)) ^ 2)

def vecF (X : Lie E a) (f : Lie E a → ℂ) : Lie E a → ℂ := fun y => fderiv ℝ f y (rmul X y)

def lapF (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    (vecF E a (toL (Matrix.single i j (atEmb τ 1))) (vecF E a (toL (Matrix.single i j (atEmb τ 1))) f) +
      vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) (vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) f))

def polyF (p : Polynomial ℂ) (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (lapF E a)^[k] f

end GlobalTheory.HCAlpha

end
