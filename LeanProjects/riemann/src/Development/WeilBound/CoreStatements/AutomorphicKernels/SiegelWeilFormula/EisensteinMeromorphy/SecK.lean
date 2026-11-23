import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.ThetaLifts.LatticeBasics.SecLaw

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.Khead

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem secK : SecK := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  obtain ⟨c1, c2⟩ := sec_cont_law d.ok.dbl hΦ.1
  refine ⟨c1, fun p t x hp => ?_, ?_⟩
  · simp only [SD.sec0, s0]
    exact c2 p t x hp
  · have := hΦ.2
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)).map
      (LinearMap.pi fun x => d.l ∘ₗ d.om x)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, funext fun x => by simp [SD.sec0, map_mul]⟩

end PositivityTheory.SiegelWeilFormula.Khead
