import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def Bint {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (Eis : ℂ → UA σ X.J → ℂ) (s : ℂ) (h : UA σ W.J) : ℂ :=
  ∫ g in M.dom, theta om Φ g h * Eis s g ∂M.μ

variable (W₁) in

def HasLawC {d d₁ : ℕ} {W : Spc F E d} (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℂ)
    (T : UA σ W.J → ℂ) : Prop :=
  ∀ t m, IsLevi (W₁ := W₁) H' t 1 m → ∀ h, T (m * h) = (χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * T h

def IsReps {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (T : Set (UA σ J)) (x : Fin n → E) : Prop :=
  T ⊆ ratU σ J ∧ ∀ γ ∈ ratU σ J, ∃! t, t ∈ T ∧ ∃ l : (AE F E)ˣ, mat (γ * t⁻¹) *ᵥ incV F x = l.1 • incV F x

def LocUnifSum {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (f : UA σ J → ℂ) (T : Set (UA σ J)) : Prop :=
  ∀ S : Set (UA σ J), IsCompact S → ∃ b : T → ℝ, Summable b ∧ ∀ t : T, ∀ h ∈ S, ‖f (t.1 * h)‖ ≤ b t

def EisGood {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : ℕ) (Eis : ℂ → UA σ J → ℂ) : Prop :=
  (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → UA σ J → ℂ) (C : ℝ) (N : ℕ), U ∈ 𝓝 s₀ ∧
      (∀ s ∈ U, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧ (∀ g, DifferentiableOn ℂ (Hol · g) U) ∧
      ∀ s ∈ U, ∀ g, ‖Hol s g‖ ≤ C * (ht g : ℝ) ^ N) ∧
    ∃ U ∈ 𝓝 (-((((b + 2 : ℕ) : ℂ) - 1) / 2)), ∃ (C : ℝ) (N : ℕ), ∀ g, DifferentiableOn ℂ (Eis · g) U ∧
      (∀ s ∈ U, ‖Eis s g‖ ≤ C * (ht g : ℝ) ^ N) ∧ Eis (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) g = 1

example {d d₁ : ℕ} {W : Spc F E d} (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℂ) :
    HasLawC (σ := σ) (W := W) W₁ H' χ z 0 := fun _ _ _ _ => by simp

end GlobalTheory.ConeSmallCT

end
