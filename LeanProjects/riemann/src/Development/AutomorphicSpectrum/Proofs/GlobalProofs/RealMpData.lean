import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

noncomputable section

open MeasureTheory Complex Matrix
open scoped Real SchwartzMap ComplexConjugate ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open GlobalTheory.RealWeil

variable {l : Type} [Fintype l] [DecidableEq l]

def RealMpData {G : Type} [Group G] [TopologicalSpace G]
    (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l))
    (omS : G →* (Sch l →L[ℂ] Sch l)) : Prop :=
  (IsCoveringMap pr ∧ Function.Surjective pr ∧
    ∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧
  (∀ f : L2 l, Continuous fun g => om g f) ∧
  (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
    om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧
  (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧
  (∀ (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
    (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
    ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2)) ∧
  (∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) ∧
    ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((quad X f).toLp 2) 0)

def FlowOf {G : Type} [Group G] [TopologicalSpace G] (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l))
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (γ : ℝ → G) : Prop :=
  Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
    ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((quad X f).toLp 2) 0

omit [DecidableEq l] in

def gaussFun (Z : Matrix l l ℂ) (x : EuclideanSpace ℝ l) : ℂ :=
  cexp (-(π : ℂ) * ∑ j, ∑ k, Z j k * (x j : ℂ) * (x k : ℂ))

omit [DecidableEq l] in

def GaussAdm (Z : Matrix l l ℂ) : Prop := Zᵀ = Z ∧ (Z.map Complex.re).PosDef

omit [Fintype l] [DecidableEq l] in

def realify (Z : Matrix l l ℂ) : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  fromBlocks (Z.map Complex.re) (-(Z.map Complex.im)) (Z.map Complex.im) (Z.map Complex.re)

omit [Fintype l] [DecidableEq l] in

def dilX (S : Matrix l l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := fromBlocks S 0 0 (-S)

omit [Fintype l] [DecidableEq l] in

def chirpX (C : Matrix l l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := fromBlocks 0 0 C 0

end GlobalTheory.CompanionTheory.Hypotheses₂
