import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

noncomputable section

open Matrix

namespace PositivityTheory.Tls2.Iua

def IwaOn {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G,
    g = k * s ∧ (Uᴴ * s * U).BlockTriangular id

def AdmG {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn G σ → Formalism.MainNotions.S.IsIrredOn G σ →
    ∀ (S : Submodule ℂ H) [FiniteDimensional ℂ S], GlobalTheory.LinRed.IsKStable G σ S → ∀ v ∈ S,
      ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ Module.finrank ℂ Y ≤ Module.finrank ℂ S ^ 2 + 1 ∧ v ∈ Y ∧
        ∀ T : H →L[ℂ] H, (∀ k ∈ GlobalTheory.LinRed.maxCpt G, ∀ u, T (σ k u) = σ k (T u)) → ∀ y ∈ Y, T y ∈ Y

def IUAIwa : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), GlobalTheory.LinRed.IsLinRed G → IwaOn G →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn G σ → Formalism.MainNotions.S.IsIrredOn G σ →
        GlobalTheory.LinRed.IsAdmOn G σ

end PositivityTheory.Tls2.Iua
