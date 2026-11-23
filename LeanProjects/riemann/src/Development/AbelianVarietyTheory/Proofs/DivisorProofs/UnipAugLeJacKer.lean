import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero

noncomputable section

namespace GlobalTheory.JacquetLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}

def unipAug (om : Rep σ X W) (H' : Plane E d d₁) (v : Pl F) : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ) :=
  Submodule.span ℂ {z | ∃ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) ∧ ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v),
    ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, u)) φ₀ φ₁ ∧ z = φ₁ - φ₀}

def jacKer (om : Rep σ X W) (H' : Plane E d d₁) (v : Pl F) : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ) :=
  augAt om v ⊔ unipAug om H' v

theorem augAt_le_jacKer (om : Rep σ X W) (H' : Plane E d d₁) (v : Pl F) : augAt om v ≤ jacKer om H' v :=
  le_sup_left

theorem unipAug_le_jacKer (om : Rep σ X W) (H' : Plane E d d₁) (v : Pl F) : unipAug om H' v ≤ jacKer om H' v :=
  le_sup_right

theorem jacKer_le_ker (om : Rep σ X W) (H' : Plane E d d₁) (v : Pl F)
    (ℓ : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (h₁ : augAt om v ≤ LinearMap.ker ℓ)
    (h₂ : ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → ∀ φ₀ ∈ SB (Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, u)) φ₀ φ₁ → ℓ φ₁ = ℓ φ₀) :
    jacKer om H' v ≤ LinearMap.ker ℓ := by
  refine sup_le h₁ ?_
  rw [unipAug, Submodule.span_le]
  rintro z ⟨u, hu, huv, φ₀, h0, φ₁, h1, hact, rfl⟩
  simp [LinearMap.mem_ker, map_sub, h₂ u hu huv φ₀ h0 φ₁ h1 hact]

end GlobalTheory.JacquetLine
