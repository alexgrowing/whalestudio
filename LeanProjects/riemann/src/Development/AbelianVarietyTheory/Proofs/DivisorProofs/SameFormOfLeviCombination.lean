import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianEqOfLeviFormEqStatement
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

namespace GlobalTheory.ChernWeilLine

theorem sameForm_combPot_of_levi : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {ι : Type} [Fintype ι]
    (P : LocPot X) (Q : ι → LocPot X) (t : ι → ℝ), (∀ i, IsPotential A (Q i)) →
    (∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A P j y w = ∑ i, t i * leviAt A (Q i) j y w) →
    GlobalTheory.SameForm A P (InhabCalc.combPot Q t 0) := by
  intro e X _ A ι _ P Q t hQ hP j y hy
  have h0 : A.Smooth (0 : X → ℝ) := fun k => contDiffOn_const
  have hpot := InhabCalc.isPotential_combPot A Q hQ t 0 h0
  have hψ := potSmoothAt A _ hpot ((A.chart j).symm y) j ⟨hy, (InhabCalc.combPot Q t 0).mem_U _⟩
  have hL := LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.leviAt_combPot e X A ι Q t 0 hQ h0 j y hy
  refine GlobalTheory.T.hessian_eq_of_levi_form_eq hψ fun w => ?_
  have hz : leviAt A (LocPot.ofFun (0 : X → ℝ)) j y w = 0 := by
    simp [leviAt, LocPot.ofFun, levi]
  have := hL w
  rw [hz, add_zero] at this
  exact (hP j y hy w).trans this.symm

end GlobalTheory.ChernWeilLine
