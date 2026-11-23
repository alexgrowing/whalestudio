import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareSt

def WeilConvergence : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
    ∀ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) → X.rank < 2 * (M.rank - p) →
    ∀ ν 𝓕, IsHaarFD M ν 𝓕 → ∀ Φ, IsThetaFunO ψ (sgn ε M) X Φ → ModInt θ ω ν 𝓕 Φ

def LocalMatching : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (q : PolF D X.rank W.rank →ₗ[ℂ] Pr) (q' : PolF D X.rank W₁.rank →ₗ[ℂ] Pr),
      Function.Surjective q ∧ Function.Surjective q' ∧
      ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
        (∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') ∧
        ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
          ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO W X → ℂ) →ₗ[ℂ] Pf) (r' : (WO W₁ X → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
            (∀ x, ∃ f, IsFinF ψ θ true A B f ∧ r f = x) ∧ (∀ x, ∃ f, IsFinF ψ θ false A₁ B f ∧ r' f = x) ∧
            (∀ f, IsFinF ψ θ true A B f → ∀ P, p (fockF ψ θ true A B f P) = e (q P ⊗ₜ r f)) ∧
            ∀ f, IsFinF ψ θ false A₁ B f → ∀ P, p' (fockF ψ θ false A₁ B f P) = e (q' P ⊗ₜ r' f)

def ThetaIntegralsAgree : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ν 𝓕 ν₁ 𝓕₁, IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ' ∈ algF ψ θ false A₁ B, ∃ Φ₀ ∈ algF ψ θ false A₁ B,
        Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B) ∧ ModInt θ ωB ν₁ 𝓕₁ Φ₀ ∧
        ∀ Φ ∈ algF ψ θ true A B, p Φ = p' Φ₀ → thetaInt ωA ν 𝓕 Φ = c • thetaInt ωB ν₁ 𝓕₁ Φ₀

end GlobalTheory.SquareSt

end
