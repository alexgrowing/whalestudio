import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdeleHaar

theorem exists_haar_integral_one : ∀ (F : Type) [Field F] [NumberField F],
    ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧
      lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 := by
  intro F _ _
  have : BorelSpace (Af F) := ⟨rfl⟩
  have hset : ({x | ∀ v, x v ∈ v.adicCompletionIntegers F} : Set (Af F)) =
      (GroundTheory.Global.integralFiniteAdelesPositiveCompacts F :
        Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    exact GroundTheory.Global.mem_integralFiniteAdeles.symm
  refine ⟨Measure.addHaarMeasure (GroundTheory.Global.integralFiniteAdelesPositiveCompacts F),
    inferInstance, ?_⟩
  rw [hset]
  exact Measure.addHaarMeasure_self

end GlobalTheory.CompanionTheory.AdeleHaar
