import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Development

noncomputable section

namespace LocMassOrdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance isTopRing_tens (v : HeightOneSpectrum (𝓞 F)) : IsTopologicalRing (Fv F v ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing (Fv F v) (Fv F v ⊗[F] E)

instance isTopGroup_HA (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : IsTopologicalGroup (HA (Fv F v) σ J) :=
  inferInstanceAs (IsTopologicalGroup (HR (Fv F v) σ J))

instance borel_HA (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : BorelSpace (HA (Fv F v) σ J) := ⟨rfl⟩

example (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    MeasurableMul (HA (Fv F v) σ J) := inferInstance

end LocMassOrdW
