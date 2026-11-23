import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.HaarCoord

theorem haar_coord_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : Type) [Fintype ι] (b : Module.Basis ι F E) (d : ℕ)
    (μ : @Measure (Fin d → AE F E) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ ν : @Measure (Fin d × ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν ∧
      ∀ g : (Fin d × ι → AF F) → ℂ,
        (Integrable g ν → Integrable (fun u : Fin d → AE F E => g (fun p => (Algebra.TensorProduct.basis (AF F) b).repr (u p.1) p.2)) μ) ∧
        ∫ u, g (fun p => (Algebra.TensorProduct.basis (AF F) b).repr (u p.1) p.2) ∂μ = ∫ t, g t ∂ν := by
  intro F E _ _ _ _ _ ι _ b d μ hμ
  letI mA : MeasurableSpace (Fin d → AE F E) := borel _
  haveI : BorelSpace (Fin d → AE F E) := ⟨rfl⟩
  letI mB : MeasurableSpace (Fin d × ι → AF F) := borel _
  haveI : BorelSpace (Fin d × ι → AF F) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  haveI : IsTopologicalAddGroup (AE F E) := IsModuleTopology.topologicalAddGroup (AF F) (AE F E)
  set B := Algebra.TensorProduct.basis (AF F) b with hB
  let L : (Fin d → AE F E) ≃ₗ[AF F] (Fin d × ι → AF F) :=
    { toFun := fun u p => B.repr (u p.1) p.2
      invFun := fun t i => B.equivFun.symm (fun j => t (i, j))
      map_add' := by intro u v; funext p; simp
      map_smul' := by intro r u; funext p; simp
      left_inv := by
        intro u; funext i
        exact B.equivFun.symm_apply_apply (u i)
      right_inv := by
        intro t; funext p
        exact congrFun (B.equivFun.apply_symm_apply (fun j => t (p.1, j))) p.2 }
  have hc : Continuous L := IsModuleTopology.continuous_of_linearMap L.toLinearMap
  have hs : Continuous L.symm := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap
  let h : (Fin d → AE F E) ≃ₜ (Fin d × ι → AF F) := ⟨L.toEquiv, hc, hs⟩
  have hH : (μ.map L.toAddEquiv).IsAddHaarMeasure := L.toAddEquiv.isAddHaarMeasure_map μ hc hs
  have hmap : μ.map L.toAddEquiv = μ.map h.toMeasurableEquiv := rfl
  refine ⟨μ.map h.toMeasurableEquiv, hmap ▸ hH, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · exact (integrable_map_equiv h.toMeasurableEquiv g).1 hg
  · exact (integral_map_equiv h.toMeasurableEquiv g).symm

end GlobalTheory.HaarCoord
