import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def coneI (B : Base F E) {a b : ℕ} (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)) (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b))
    (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ) (ν : Chr F E) (om' : Rep σ G.V' G.W)
    (om₁' : Rep σ G₁.V' G₁.W) (Φ' : Fn F (b + 2) (a + (b + 2))) (z : ℂ) (h : UA σ G.W.J) : ℂ :=
  ∫ k, ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1 * (ν l : ℂ) *
    ((absE F E l : ℝ) : ℂ) ^ z ∂μ ∂μK

def IsIwaHt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J)) (x : Fin n → E) (hf : UA σ J → ℝ) : Prop :=
  ∀ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K → mat p *ᵥ incV F x = l.1 • incV F x → hf (p * k) = absE F E l

def IsEisSer {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J)) (x : Fin n → E) (Eis : ℂ → UA σ J → ℂ) :
    Prop :=
  ∃ hf : UA σ J → ℝ, IsIwaHt K x hf ∧
    (∀ g, ∃ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F x = l.1 • incV F x ∧ g = p * k) ∧
    ∀ T : Set (UA σ J), T ⊆ ratU σ J → (∀ γ ∈ ratU σ J, ∃! t, t ∈ T ∧ ∃ l : (AE F E)ˣ,
        mat (γ * t⁻¹) *ᵥ incV F x = l.1 • incV F x) →
      ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
        HasSum (fun t : T => (hf (t.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s g)

def EisAtMinusRho : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K → ∃ Eis : ℂ → UA σ G.V'.J → ℂ, IsEisSer K H.x Eis ∧
      (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → UA σ G.V'.J → ℂ) (C : ℝ) (N : ℕ), U ∈ 𝓝 s₀ ∧
        (∀ s ∈ U, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧ (∀ g, DifferentiableOn ℂ (Hol · g) U) ∧
        ∀ s ∈ U, ∀ g, ‖Hol s g‖ ≤ C * (ht g : ℝ) ^ N) ∧
      ∃ U ∈ 𝓝 (-((((b + 2 : ℕ) : ℂ) - 1) / 2)), ∃ (C : ℝ) (N : ℕ), ∀ g, DifferentiableOn ℂ (Eis · g) U ∧
        (∀ s ∈ U, ‖Eis s g‖ ≤ C * (ht g : ℝ) ^ N) ∧ Eis (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) g = 1

end GlobalTheory.ConeSmall

end
