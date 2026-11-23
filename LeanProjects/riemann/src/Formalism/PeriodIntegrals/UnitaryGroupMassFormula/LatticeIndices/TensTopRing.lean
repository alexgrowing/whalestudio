import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MeasBAll

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct

theorem tens_topRing {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) : IsTopologicalRing (Fv F v ⊗[F] E) := by
  haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := inferInstance
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  first
    | exact IsModuleTopology.topologicalRing (Fv F v) _
    | exact IsModuleTopology.isTopologicalRing (Fv F v) _
    | exact IsModuleTopology.Module.topologicalRing (Fv F v) _

theorem ha_contMul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) :
    ContinuousMul (HA (Fv F v) σ J) := by
  haveI := tens_topRing (F := F) (E := E) v
  first
    | infer_instance
    | (unfold HA; infer_instance)
    | (show ContinuousMul (HR (Fv F v) σ J); infer_instance)

theorem stTop {D : D7} (X : HidaSetting D) (p : TypX X) : StTop X p := by
  refine ⟨ha_contMul _ _ _, ?_⟩
  first
    | exact ⟨rfl⟩
    | (unfold HAp HA; infer_instance)
    | (haveI := tens_topRing (F := X.B.I.F) (E := X.B.I.E) p.1; unfold HAp HA; infer_instance)

end MassDataIdxSteps
