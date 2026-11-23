import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published

def LeviCentreInducedUnitary : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
    (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J →
    ∀ ψ : UA σ Y.J → ℂ, (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) →
    ∀ χ : Chr F E, Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
    (∀ t m, IsLevi (W₁ := Y₁) H t 1 m → ∀ x, ψ (m * x) = (χ t : ℂ) * ψ x) →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    ∀ φ : GAd σ (c • Y.J.map σ) → ℂ, (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) →
      GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ →
    ∀ V : Submodule ℂ (GAd σ (c • Y₁.J.map σ) → ℂ), FiniteDimensional ℂ V → (∀ v ∈ V, GlobalTheory.UAut.IsSm σ (c • Y₁.J.map σ) v) →
      (∀ v ∈ V, ∀ z, GlobalTheory.UAut.IsCentral σ (c • Y₁.J.map σ) z → GlobalTheory.UAut.dop z v ∈ V) →
    ∀ Kc : Set (UA σ Y.J), (∀ x : UA σ Y.J, ∃ u ∈ unip σ Y H, ∃ t h₁ m, IsLevi (W₁ := Y₁) H t h₁ m ∧ ∃ k ∈ Kc, x = u * m * k) →
      (∀ k ∈ Kc, ∃ v ∈ V, ∀ (h₁ : UA σ Y₁.J) (m : UA σ Y.J) (g' : GAd σ (c • Y₁.J.map σ)),
        IsLevi (W₁ := Y₁) H 1 h₁ m → h₁.1 = g'.1 → v g' = ψ (m * k)) →
      FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ})

end GlobalTheory.Published

end
