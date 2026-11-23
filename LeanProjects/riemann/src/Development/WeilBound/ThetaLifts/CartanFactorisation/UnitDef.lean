import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def RadMaxAt (B : Base F E) (M : Model σ X W) (om : Rep σ X W) : Prop :=
  ∀ β : M.Pol B.ψ B.emb →ₗ⋆[ℂ] M.Pol B.ψ B.emb →ₗ[ℂ] ℂ, (∀ x y, β x y = starRingEnd ℂ (β y x)) →
    (∀ γ ∈ Lines σ X, ∀ x y : M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) x.1 y.1 → β y = 0) →
    (∀ δ ∈ Lines σ W, ∀ x x₁ y y₁ : M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) x.1 x₁.1 →
      ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) y.1 y₁.1 → β x₁ y + β x y₁ = 0) →
    ∀ P : Submodule ℂ (M.Pol B.ψ B.emb), LinearMap.ker β ≤ P →
      (∀ δ ∈ Lines σ W, ∀ x ∈ P, ∀ y : M.Pol B.ψ B.emb,
        ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) x.1 y.1 → y ∈ P) → P ≤ LinearMap.ker β ∨ P = ⊤

def RadMax : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    RadMaxAt B G.M om ∧ RadMaxAt B G.M' om'

end PositivityTheory.ThKF

end
