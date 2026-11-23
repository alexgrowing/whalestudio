import Mathlib
import Formalism.PeriodIntegrals.LocLatEq

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

def ιO {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) (d : 𝓞 F) : A.Ep :=
  A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E)

def IntP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p),
    ∀ a : E, A.ιE a ∈ A.O → ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ b : 𝓞 E,
      ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) * a = b

end PI.LocLatEq.W
