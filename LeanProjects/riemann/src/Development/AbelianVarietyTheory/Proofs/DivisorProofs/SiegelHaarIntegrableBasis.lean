import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.SiegelConv

open GlobalTheory.SiegelAvg

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)

def basisLEquiv : (Fin n × Fin (Module.finrank F E) → AF F) ≃ₗ[AF F] (Fin n → AE F E) :=
  (LinearEquiv.curry (AF F) (AF F) (Fin n) (Fin (Module.finrank F E))).trans
    (LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.symm)

theorem basisLEquiv_apply (t : Fin n × Fin (Module.finrank F E) → AF F) :
    basisLEquiv F E n t = basisMap F E n t := by
  funext j
  simp [basisLEquiv, basisMap, Module.Basis.equivFun_symm_apply, Algebra.TensorProduct.basis_apply, inclR]

local instance topRingAEBasis : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

def basisCLEquiv : (Fin n × Fin (Module.finrank F E) → AF F) ≃L[AF F] (Fin n → AE F E) where
  toLinearEquiv := basisLEquiv F E n
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (basisLEquiv F E n).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap (basisLEquiv F E n).symm.toLinearMap

theorem integrable_of_basisMap (f : (Fin n → AE F E) → ℂ) (μ : @Measure (Fin n → AE F E) (borel _))
    (hμ : IsHaarB μ)
    (hf : ∀ ν : @Measure (Fin n × Fin (Module.finrank F E) → AF F) (borel _), IsHaarB ν →
      (letI : MeasurableSpace (Fin n × Fin (Module.finrank F E) → AF F) := borel _;
        Integrable (fun t => f (basisMap F E n t)) ν)) :
    (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable f μ) := by
  letI mX : MeasurableSpace (Fin n × Fin (Module.finrank F E) → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin (Module.finrank F E) → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (Fin n → AE F E) := borel _
  haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  set T := basisCLEquiv F E n with hT
  have hTf : ∀ t, T t = basisMap F E n t := basisLEquiv_apply F E n
  haveI hν : (μ.map T.symm).IsAddHaarMeasure := ContinuousLinearEquiv.isAddHaarMeasure_map T.symm μ
  have h1 := hf (μ.map T.symm) hν
  have hme : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hmap : (μ.map T.symm).map T = μ := by
    rw [Measure.map_map T.continuous.measurable T.symm.continuous.measurable]
    have : (T ∘ T.symm) = id := funext fun y => T.apply_symm_apply y
    rw [this, Measure.map_id]
  rw [← hmap, hme.integrable_map_iff]
  simpa [Function.comp_def, hTf] using h1

end GlobalTheory.SiegelConv

theorem GlobalTheory.SiegelConv.integrable_basisMap_main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (f : (Fin n → AE F E) → ℂ) (μ : @Measure (Fin n → AE F E) (borel _)), GlobalTheory.SiegelAvg.IsHaarB μ →
    (∀ ν : @Measure (Fin n × Fin (Module.finrank F E) → AF F) (borel _), GlobalTheory.SiegelAvg.IsHaarB ν →
      (letI : MeasurableSpace (Fin n × Fin (Module.finrank F E) → AF F) := borel _; Integrable (fun t => f (GlobalTheory.SiegelConv.basisMap F E n t)) ν)) →
    (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable f μ) :=
  fun F E _ _ _ _ _ n f μ hμ hf => GlobalTheory.SiegelConv.integrable_of_basisMap F E n f μ hμ hf
