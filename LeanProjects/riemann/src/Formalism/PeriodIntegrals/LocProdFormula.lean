import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef

noncomputable section

open NumberField IsDedekindDomain

namespace PI

def LocProdFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (sig : E →ₐ[F] E) (atP : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
      (M : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.Model (atP p).Fp (atP p).Ep), (∀ p, (M p).OK) →
      ∀ x : E, x ≠ 0 → ∏ᶠ p, (M p).modK ((atP p).ιE x) = (((|Algebra.norm ℚ x| : ℚ)) : ℝ)⁻¹

end PI
