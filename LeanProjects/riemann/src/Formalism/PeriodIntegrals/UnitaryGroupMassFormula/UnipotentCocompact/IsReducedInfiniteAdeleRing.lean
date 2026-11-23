import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCocompact.AdeleUnip

open NumberField IsDedekindDomain
open scoped RestrictedProduct

namespace PI.UnipCocptD

open PI.UnipApproxD

instance isReduced_finiteAdeleRing (F : Type) [Field F] [NumberField F] :
    IsReduced (FiniteAdeleRing (𝓞 F) F) := by
  have : IsReduced (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]) := by
    refine ⟨fun x ⟨k, hk⟩ => ?_⟩
    apply RestrictedProduct.ext
    intro v
    have h2 : (x v) ^ k = 0 := by
      rw [← RestrictedProduct.pow_apply, hk]
      rfl
    rw [IsReduced.eq_zero (x v) ⟨k, h2⟩]
    rfl
  exact this

instance isReduced_infiniteAdeleRing (F : Type) [Field F] [NumberField F] :
    IsReduced (InfiniteAdeleRing F) :=
  inferInstanceAs (IsReduced ((v : InfinitePlace F) → v.Completion))

instance isReduced_adeleRing (F : Type) [Field F] [NumberField F] :
    IsReduced (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (IsReduced (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end PI.UnipCocptD
