import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HasInfExpF

noncomputable section

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def UnramInert (σ : E →ₐ[F] E) (η : (AF F ⊗[F] E)ˣ →* Circle) : Prop :=
  ∀ x : (AEF F E)ˣ, infPartF F E (x : AEF F E) = 1 → (∀ e, IsSplitIdemF σ e → e * (x : AEF F E) = e) →
    finPartF F E (x : AEF F E) ∈ intAEF F E → finPartF F E ((x⁻¹ : (AEF F E)ˣ) : AEF F E) ∈ intAEF F E → η x = 1

end PositivityTheory.ThKW

end
