import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FourierJacobiCoeffLinearBoundedSections
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie

theorem mem_domSpan_iff_of_closed {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (A : Set (Frame X.Ψ r → ℂ)) (h0 : 0 ∈ A) (hadd : ∀ P ∈ A, ∀ Q ∈ A, P + Q ∈ A)
    (hsmul : ∀ (a : ℂ), ∀ P ∈ A, a • P ∈ A) (hind : ∀ f ∈ A, X.dom.indicator f ∈ A) (g : Frame X.Ψ r → ℂ) :
    g ∈ domSpan X A ↔ g ∈ A ∧ ∀ x ∉ X.dom, g x = 0 := by
  constructor
  · intro hg
    unfold domSpan at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      exact ⟨hind f hf, fun x hx => Set.indicator_of_notMem hx _⟩
    | zero => exact ⟨h0, fun _ _ => rfl⟩
    | add P Q _ _ hP hQ =>
      exact ⟨hadd _ hP.1 _ hQ.1, fun x hx => by rw [Pi.add_apply, hP.2 x hx, hQ.2 x hx, add_zero]⟩
    | smul a P _ hP =>
      exact ⟨hsmul a _ hP.1, fun x hx => by rw [Pi.smul_apply, hP.2 x hx, smul_zero]⟩
  · rintro ⟨hg, hz⟩
    refine Submodule.subset_span ⟨g, hg, ?_⟩
    funext x
    by_cases hx : x ∈ X.dom
    · exact Set.indicator_of_mem hx _
    · exact (Set.indicator_of_notMem hx _).trans (hz x hx).symm

theorem indicator_mem_SS_and_domSpan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (c : ℝ), (∀ f ∈ X.SS la, X.dom.indicator f ∈ X.SS la) ∧ (∀ f ∈ X.SSgt la c, X.dom.indicator f ∈ X.SSgt la c) ∧ (∀ g, g ∈ domSpan X (X.SS la) ↔ g ∈ X.SS la ∧ ∀ x ∉ X.dom, g x = 0) ∧ (∀ g, g ∈ domSpan X (X.SSgt la c) ↔ g ∈ X.SSgt la c ∧ ∀ x ∉ X.dom, g x = 0) := by
  intro E _ _ _ r X la c
  have h1 : ∀ f ∈ X.SS la, X.dom.indicator f ∈ X.SS la := fun f hf =>
    (GlobalTheory.DomCongr.bddSec_cusp_congr E r X la f _ (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hf
  have h2 : ∀ f ∈ X.SSgt la c, X.dom.indicator f ∈ X.SSgt la c := by
    intro f hf
    refine ⟨h1 f hf.1, fun ξ hξ ν hν x hx => ?_⟩
    have e := GlobalTheory.fj_eq_sum_of_eqOn_dom E r X la 1 (fun _ => 1) (fun _ => f) (X.dom.indicator f)
      (fun _ => hf.1.1) (fun y hy => by simp [Set.indicator_of_mem hy]) ξ hξ ν x hx
    rw [e]
    simp [hf.2 ξ hξ ν hν x hx]
  obtain ⟨⟨a0, a1, a2⟩, -, ⟨b0, b1, b2⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X la la c
  exact ⟨h1, h2, mem_domSpan_iff_of_closed X _ a0 a1 a2 h1, mem_domSpan_iff_of_closed X _ b0 b1 b2 h2⟩

end GlobalTheory.UpTie
