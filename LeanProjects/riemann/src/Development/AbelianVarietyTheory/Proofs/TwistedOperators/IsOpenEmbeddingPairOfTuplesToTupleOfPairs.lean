import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem zipHom_isOpenEmbedding : ∀ (κ X Y : Type) [Fintype κ] [AddCommGroup X] [TopologicalSpace X]
    [AddCommGroup Y] [TopologicalSpace Y], IsOpenEmbedding (zipHom κ X Y) := by
  intro κ X Y _ _ _ _ _
  let e : ((κ → X) × (κ → Y)) ≃ₜ (κ → X × Y) :=
    { toFun := fun p i => (p.1 i, p.2 i)
      invFun := fun q => (fun i => (q i).1, fun i => (q i).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i =>
        ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
      continuous_invFun :=
        (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
          (continuous_pi fun i => continuous_snd.comp (continuous_apply i)) }
  exact e.isOpenEmbedding

end GlobalTheory.ModuLR
