import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionHolds

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

open NumberField in

theorem _root_.GlobalTheory.bddSec_mul_and_constTerm_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r),
      ∀ (la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ), X.IsBddSec la P → X.IsBddSec la' Q →
        X.IsBddSec (la + la') (P * Q) ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom,
          X.fj (la + la') ξ 0 (P * Q) x = X.fj la ξ 0 P x * X.fj la' ξ 0 Q x := by
  intro E _ _ _ r X la la' P Q hP hQ
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_mul X hP hQ, fun ξ hξ x hx => ?_⟩
  have h3e : @_root_.ReciprocityTheory.ChartRestriction.G.FD.CoefficientConvolution E _ _ _ := _root_.ReciprocityTheory.ChartRestriction.G.FD.coefficientConvolution_holds
  have hm3d : @_root_.ReciprocityTheory.ChartRestriction.G.FD.ModerateCoefficientPositivity E _ _ _ := _root_.ReciprocityTheory.ChartRestriction.G.FD.moderateCoefficientPositivity_holds
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.CoefficientConvolution at h3e
  have hsum := h3e r X la la' P Q hP.1 hQ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.mod_of_bdd X hP) (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.mod_of_bdd X hQ) ξ hξ x hx 0
  have hzero : ∀ ν' ≠ (0 : ↥X.Ψ → ℝ), X.fj la ξ ν' P x * X.fj la' ξ (0 - ν') Q x = 0 := by
    intro ν' hν'
    by_contra hne
    apply hν'
    have h1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd X hm3d hP hξ ν' hx (left_ne_zero_of_mul hne)
    have h2 := _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd X hm3d hQ hξ (0 - ν') hx (right_ne_zero_of_mul hne)
    funext τ
    have a := h1 τ
    have b := h2 τ
    simp only [zero_sub, Pi.neg_apply] at b
    simp only [Pi.zero_apply]
    linarith
  have hs := hasSum_single (f := fun ν' => X.fj la ξ ν' P x * X.fj la' ξ (0 - ν') Q x) 0 hzero
  simpa using hsum.unique hs

end GlobalTheory
