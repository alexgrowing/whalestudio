import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitStab
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.G

theorem split_integral_completion (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (h : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) : SplitInt v spl :=
  split_integral_local F E v spl h

end Formalism.L2.G
