import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealActs

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def DerOn (N : Submodule ℂ (SInf F κ)) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, ActsD (evI F) T f f₁ ↔ f₁ = D f

def OpOn (N : Submodule ℂ (SInf F κ)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, Acts (evI F) T f f₁ ↔ f₁ = D f

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def PolActs (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) : Prop :=
  (∀ γ ∈ Lines σ X, DerOn (M.Pol B.ψ B.emb) (fun t => om (γ (Multiplicative.ofAdd t), 1))) ∧
  (∀ k ∈ KInf σ X B.emb, OpOn (M.Pol B.ψ B.emb) (om (k, 1))) ∧
  (∀ γ ∈ Lines σ W, DerOn (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t)))) ∧
  ∀ k ∈ KInf σ W B.emb, OpOn (M.Pol B.ψ B.emb) (om (1, k))

def KerStab (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f = 0 → p f₁ = 0) ∧
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (om (1, k)) f f₁ → p f = 0 → p f₁ = 0

def Irred (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  ∀ N : Submodule ℂ P,
    (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N) → N = ⊥ ∨ N = ⊤

end GlobalTheory.RealActs

end
