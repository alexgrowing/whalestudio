import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace Formalism.L2.SG.Pf

def PsiTrCore : Prop :=
  ∀ (I : AutInst) (ψ : I.E ⊗[I.F] Af I.F → ℂ), (∀ x y, ψ (x + y) = ψ x * ψ y) →
    (∀ x ∈ IntAf I.F I.E, ψ x = 1) →
    (∀ x : I.E, ψ (Formalism.UG.inclE (F := I.F) (Af I.F) x) *
      ∏ v, Complex.exp (2 * Real.pi * Complex.I * (I.φ v x + star (I.φ v x))) = 1) →
    ∀ y : I.E, (∀ o : 𝓞 I.E, ∃ m : ℤ, Algebra.trace ℚ I.E ((o : I.E) * y) = m) →
      ∀ t ∈ IntAf I.F I.E, ψ (t * Formalism.UG.inclE (F := I.F) (Af I.F) y) = 1

def DdTraceCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∀ y ∈ ((((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      ∀ o : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E ((o : E) * y) = m

end Formalism.L2.SG.Pf
