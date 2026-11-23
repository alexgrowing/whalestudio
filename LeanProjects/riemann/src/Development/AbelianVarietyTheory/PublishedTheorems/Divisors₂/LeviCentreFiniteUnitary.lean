import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published

def LeviCentreFiniteUnitary : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
    (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y.J.det ≠ 0 →
    Y₁.J.det ≠ 0 → ∀ ψ : UA σ Y.J → ℂ, (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    (∀ φ : GAd σ (c • Y.J.map σ) → ℂ, (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) →
      GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ ∧
        FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ})) →
    ∀ (h : UA σ Y.J) (g : UA σ Y₁.J → ℂ), (∀ h₁ m, IsLevi (W₁ := Y₁) H 1 h₁ m → g h₁ = ψ (m * h)) →
    ∀ φ₁ : GAd σ (c • Y₁.J.map σ) → ℂ, (∀ (g₁ : UA σ Y₁.J) (g' : GAd σ (c • Y₁.J.map σ)), g₁.1 = g'.1 → φ₁ g' = g g₁) →
      FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y₁.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ₁})

end GlobalTheory.Published

end
