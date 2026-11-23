import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : Set (UA σ W.J) :=
  {k | k ∈ UAt σ W (evFin F v) ∧ ∀ z ∈ latHat W, mat k *ᵥ z ∈ latHat W ∧ mat k⁻¹ *ᵥ z ∈ latHat W}

theorem one_mem_KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : (1 : UA σ W.J) ∈ KAt σ W v := by
  refine ⟨fun u _ => by simp [mat], fun z hz => ?_⟩
  simp only [inv_one]
  simpa [mat] using hz

end GlobalTheory.IndLine
