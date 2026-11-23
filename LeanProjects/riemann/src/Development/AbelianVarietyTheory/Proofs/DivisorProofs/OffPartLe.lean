import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf

noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def IsTwEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f = x →
      p f₁ = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • x

def IsOffEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∃ k ∈ KInf σ W B.emb, ∃ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k ∧ ∃ c : ℂ,
    c ≠ (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) ∧ ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f = x → p f₁ = c • x

def twPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsTwEig B M om p W₁ H' χ z x}

def offPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsOffEig B M om p W₁ H' χ z x}

def KStabL (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (N : Submodule ℂ P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ k₁ ∈ KInf σ W₁ B.emb, IsLevi H' 1 k₁ k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N

theorem twPart_le (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : twPart B M om p W₁ H' χ z V ≤ V :=
  Submodule.span_le.2 fun _ hx => hx.1

end GlobalTheory.IndLine
