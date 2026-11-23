import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLatticeImage
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_open_lattice_image : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) {κ G : Type} [Fintype κ] [AddCommGroup G]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ (ℓ : G →+ (κ → Fv F v) × (κ → Fv F v)) (Γ : AddSubgroup G),
      IsOpen ((Γ.map ℓ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
      IsCompact ((Γ.map ℓ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
      (∀ w : (κ → Fv F v) × (κ → Fv F v), (∀ γ ∈ Γ, ψ₀ ((ℓ γ).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (ℓ γ).2) = 1) → w ∈ Γ.map ℓ) →
      ∀ (χ : G → ℂ) (φ φ' : (κ → Fv F v) → ℂ), φ ≠ 0 →
        (∀ γ ∈ Γ, schr ψ₀ (ℓ γ) φ = χ γ • φ) → (∀ γ ∈ Γ, schr ψ₀ (ℓ γ) φ' = χ γ • φ') → ∃ c : ℂ, φ' = c • φ := by
  first | exact @GlobalTheory.HeisUniqLoc.eigen_unique | exact GlobalTheory.HeisUniqLoc.eigen_unique | (intros; apply GlobalTheory.HeisUniqLoc.eigen_unique <;> assumption)
