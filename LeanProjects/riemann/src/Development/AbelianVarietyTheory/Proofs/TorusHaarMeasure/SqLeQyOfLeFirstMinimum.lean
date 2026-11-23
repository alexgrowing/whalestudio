import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallyComparable
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.RealPointModes

namespace GlobalTheory.FJCompare

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.RealPointModes
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def vec (i : Idx E) : X.Ψ → ℝ := modeAt X (integralBasis (maximalRealSubfield E) i)

def SignDecayOn (S : Set ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ), A ∈ S → X.IsSec la P →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-A)) →
    (∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ) ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∃ Cη : ℝ, ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom,
      (∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ‖X.fj la ξ ν P x‖ * X.nfac la x ≤
        Cη * X.la1 x ^ (-A) * Real.exp (-4 * Real.pi * (1 - η) * ∑ τ, ν τ * X.tt ξ x τ)

theorem SignDecayOn.mono {S T : Set ℝ} (h : SignDecayOn T E) (hST : S ⊆ T) : SignDecayOn S E :=
  fun r X la P C A hA => h r X la P C A (hST hA)

def ProductSupport (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ),
    X.IsSec la P → X.IsSec la' Q → X.IsModerate la P → X.IsModerate la' Q →
    ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ ν : X.Ψ → ℝ, X.fj (la + la') ξ ν (P * Q) x ≠ 0 →
      ∃ ν' : X.Ψ → ℝ, X.fj la ξ ν' P x * X.fj la' ξ (ν - ν') Q x ≠ 0

end

end GlobalTheory.FJCompare
