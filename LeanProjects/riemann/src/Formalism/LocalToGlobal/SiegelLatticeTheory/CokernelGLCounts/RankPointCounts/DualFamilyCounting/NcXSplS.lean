import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcX.LT

def SplitStr : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)), IsCMExt F E σ → ¬ IsField (Fv F v ⊗[F] E) →
    ∃ π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v,
      (∀ s, π₁ (sigR (Fv F v) σ s) = π₂ s) ∧ (∀ s, π₂ (sigR (Fv F v) σ s) = π₁ s) ∧
      (∀ c : Fv F v, π₁ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = c ∧
        π₂ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = c) ∧
      (∀ s t, π₁ s = π₁ t → π₂ s = π₂ t → s = t) ∧
      (∀ p q : Fv F v, ∃ s, π₁ s = p ∧ π₂ s = q)

end Formalism.L2.SG.Pf.NcX.LT
