import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef

noncomputable section

open IsDedekindDomain NumberField

namespace PI.StrongApproxE

def StrongApproxE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (_h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (U : ∀ p, AddSubgroup (L p).Ep), (∀ p, IsOpen (U p : Set (L p).Ep)) →
    {p | (U p : Set (L p).Ep) ≠ ((L p).O : Set (L p).Ep)}.Finite →
    ∀ x : ∀ p, (L p).Ep, {p | x p ∉ (L p).O}.Finite →
      ∃ t : E, ∀ p, (L p).ιE t - x p ∈ U p

end PI.StrongApproxE
