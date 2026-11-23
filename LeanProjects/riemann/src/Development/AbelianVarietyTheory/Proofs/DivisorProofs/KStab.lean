import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def PGen (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (V : Submodule ℂ P) : Prop :=
  ∀ N : Submodule ℂ P, V ≤ N →
    (∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ γ ∈ Lines σ W, (∃ (t : Multiplicative ℝ →* (AE F E)ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
        ∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    N = ⊤

def KStab (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (V : Submodule ℂ P) : Prop :=
  (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ V → p f₁ ∈ V) ∧
    ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ KInf σ W B.emb) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ V → p f₁ ∈ V

end GlobalTheory.IndLine
