import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open GlobalTheory.Eis

def EisConvFar {D : D7} (V : HSp D) (Φ : ℂ → GA D (dblSp V) → ℂ) : Prop :=
  ∃ t : ℝ, ∀ s : ℂ, t < s.re → LeftInv (siegelQ V) (Φ s) ∧ ∀ g, EisConv V (Φ s) g

def SiegelEisensteinDoublingContinuation : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      (EisConvFar V (flat V a φ s₁) ∧ ∀ g, Continues (eisSer V (flat V a φ s₁) g)) ∧
        ∀ s₀, ∃ k, EisRegularAt V (flat V a φ s₁) s₀ k

def SiegelEisensteinDoublingPole : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → V.rank < b →
      EisConvFar V (flat V a φ s₁) ∧ ∀ g, PoleLE (eisSer V (flat V a φ s₁) g) (((b : ℂ) - V.rank) / 2) 1

def SiegelEisDoubling : Prop := SiegelEisensteinDoublingContinuation ∧ SiegelEisensteinDoublingPole

end GlobalTheory.CompanionTheory.Hypotheses₂

end
