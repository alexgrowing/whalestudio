import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def invDiff (F : Type) [Field F] [NumberField F] : Set F :=
  {d | ∀ y : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (d * (y : F)) = z}

def invDiffAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {α | ∃ (n : ℕ) (d : Fin n → F) (x : Fin n → Af F), (∀ i, d i ∈ invDiff F) ∧ (∀ i, x i ∈ intAf F) ∧
    α = ∑ i, algebraMap F (Af F) (d i) * x i}

def StdCharExists (D : D7) : Prop :=
  (∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1)) ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ α : Af D.host.F,
      ((∀ x ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * x)) = 1) ↔ α ∈ invDiffAf D.host.F)

def CharComplete (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ S T : HSp D,
    (∀ x : WO S T, (∀ γ, ψ (symplO S T x (ratW T S γ)) = 1) → x ∈ ratL T S) ∧
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ φ : WO S T → ℂ, Continuous φ → (∀ γ w, φ (ratW T S γ + w) = φ w) →
        (∀ γ, ∫ w in 𝓕, φ w * ψ (symplO S T w (ratW T S γ)) ∂μ = 0) → φ = 0

def coefO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (f f' : WO S T → ℂ) (w : WO S T) : ℂ :=
  ∫ x in 𝓕, heisO ψ S T w f x * starRingEnd ℂ (f' x) ∂μ

def KernelId (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
    ∀ f₁ f₁' f₂ f₂' : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₁' → IsThetaFunO ψ S T f₂ →
      IsThetaFunO ψ S T f₂' → (∀ w, coefO ψ S T μ 𝓕 f₁ f₁' w = coefO ψ S T μ 𝓕 f₂ f₂' w) →
      ∀ x y, f₁ y * starRingEnd ℂ (f₁' x) = f₂ y * starRingEnd ℂ (f₂' x)

def SvNSchurO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∀ A : Module.End ℂ (WO S T → ℂ),
    (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) →
    (∀ w₀ f, IsThetaFunO ψ S T f → A (heisO ψ S T w₀ f) = heisO ψ S T w₀ (A f)) →
    (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f →
        ∫⁻ w in 𝓕, ‖A f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → A f = c • f

def SvNSchurOAll (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ S T : HSp D, SvNSchurO ψ S T

end Formalism.IndefR.Fin

end
