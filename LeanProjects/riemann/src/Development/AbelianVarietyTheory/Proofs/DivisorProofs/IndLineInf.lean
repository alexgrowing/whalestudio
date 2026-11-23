import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Fin

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsIndMap (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (A : P →ₗ[ℂ] (UA σ W.J → P₁)) : Prop where
  right : ∀ g ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
    Acts (evFin F v) (om (1, g)) φ φ₁ → ∀ h ∈ UAt σ W (evFin F v), A (p φ₁) h = A (p φ) (h * g)
  unip : ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x (u * h) = A x h
  levi : ∀ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi H' t h₁ m → m ∈ UAt σ W (evFin F v) →
    h₁ ∈ UAt σ W₁ (evFin F v) → ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), ∀ φ₁ ∈ SB (Fin n₁ × Fin d₁ → Fv F v),
    Acts (evFin F v) (om₁ (1, h₁)) φ φ₁ → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = p₁ φ →
      A x (m * h) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ φ₁

def IndLineFin (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) : Prop :=
  ∀ A A' : P →ₗ[ℂ] (UA σ W.J → P₁), IsIndMap v om om₁ p p₁ H' χ z A → IsIndMap v om om₁ p p₁ H' χ z A' →
    (∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = 0) ∨ ∃ c : ℂ, ∀ x, ∀ h ∈ UAt σ W (evFin F v), A' x h = c • A x h

end Fin

section Inf

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsFrobInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) (φ : P →ₗ[ℂ] P₁) : Prop where
  unip : ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → φ (p f₁) = 0
  lie : ∀ γ ∈ Lines σ W, ∀ γ₁ ∈ Lines σ W₁, ∀ t : Multiplicative ℝ →* (AE F E)ˣ, (∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁),
    ActsD (evI F) (fun s => om₁ (1, γ₁ (Multiplicative.ofAdd s))) g g₁ → φ (p f) = p₁ g → ∀ c : ℂ,
    HasDerivAt (fun s : ℝ => (χ (t (Multiplicative.ofAdd s)) : ℂ) *
      (((absE F E (t (Multiplicative.ofAdd s)) : ℝ) ^ z : ℝ) : ℂ)) c 0 →
      φ (p f₁) = p₁ g₁ + c • φ (p f)
  cpt : ∀ k ∈ KInf σ W B.emb, ∀ (t : (AE F E)ˣ) (k₁ : UA σ W₁.J), IsLevi H' t k₁ k → k₁ ∈ KInf σ W₁ B.emb →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁), Acts (evI F) (om₁ (1, k₁)) g g₁ → φ (p f) = p₁ g →
      φ (p f₁) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ g₁

def IndLineInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) : Prop :=
  ∀ φ φ' : P →ₗ[ℂ] P₁, IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ → IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ' →
    φ = 0 ∨ ∃ c : ℂ, φ' = c • φ

end Inf

end GlobalTheory.IndLine
