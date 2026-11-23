import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latAt {d : ℕ} (W : Spc F E d) (v : Pl F) : AddSubgroup (Fin d → AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
    ∃ y ∈ W.L, z = a • fun i => inclR (F := F) (AF F) (y i)}

def KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : Set (UA σ W.J) :=
  {h | h ∈ UAt σ W (evFin F v) ∧ ∀ z ∈ latAt W v, mat h *ᵥ z ∈ latAt W v ∧ mat h⁻¹ *ᵥ z ∈ latAt W v}

theorem one_mem_KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : (1 : UA σ W.J) ∈ KAt σ W v := by
  refine ⟨?_, fun z hz => ?_⟩
  · intro u _
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  · simp [mat, hz]

end GlobalTheory.InertSph
