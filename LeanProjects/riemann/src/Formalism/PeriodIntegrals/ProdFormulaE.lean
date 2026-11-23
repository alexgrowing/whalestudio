import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef

noncomputable section

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE

def ProdFormulaE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (_h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p),
  (∀ M : ∀ p, Formalism.MainNotions.S.Loc.Model (L p).Fp (L p).Ep, (∀ p, (M p).OK) →
    ∀ x : E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((L p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : E,
    (Function.mulSupport fun p => (L p).psiE ((L p).ιE x)).Finite ∧
    ∏ᶠ p, (L p).psiE ((L p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))))

end PI.ProdFormulaE
