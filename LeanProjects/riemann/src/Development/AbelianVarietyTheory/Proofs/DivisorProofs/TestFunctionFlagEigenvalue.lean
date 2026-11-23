import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HhPowerSumEqBoundaryFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryFormEqBlockMinusLowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockFormCurveClassDegreeSumStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

open GlobalTheory.FlagForm

theorem GlobalTheory.CovTest.hh_testF : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.ArDegree → ArCalc → RegularAlteration → ∀ (D : D7) (Y : DV.ShimX D.what₂.Tau) (hh : Fn Y),
    GlobalTheory.FlagZ.IsHh D.what₂.Tau Y.N hh → hh (testF Y) = (1 / (Y.j : ℝ) - 1 / ((Y.N : ℝ) - Y.j) - 1) * testI Y := by
  intro hP hD hA hR D Y hh h
  have e1 : hh (testF Y) = ∑ τ, formDeg (bcForm τ * toForm (curveCl D.what₂.Tau Y.N Y.j)) := by
    simp only [testF, map_sum]
    exact Finset.sum_congr rfl fun τ _ => GlobalTheory.T.hh_power_sum_eq_boundary_form hP hD hA hR _ _ hh h τ _
  have e2 : ∀ τ, formDeg (bcForm τ * toForm (curveCl D.what₂.Tau Y.N Y.j)) =
      formDeg (blkForm Y.j τ * toForm (curveCl D.what₂.Tau Y.N Y.j)) -
        formDeg (toForm (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j) : FormPol D.what₂.Tau Y.N) := by
    intro τ
    rw [GlobalTheory.T.boundary_form_eq_block_minus_low _ Y.N Y.j τ, sub_mul]
    simp only [formDeg, coeff_sub, sub_div, toForm, map_mul]
  have e3 : testI Y = ∑ τ, formDeg (toForm (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j) : FormPol D.what₂.Tau Y.N) := by
    rw [testI]
    exact Finset.sum_congr rfl fun τ _ => GlobalTheory.T.flag_degree_eq_form_degree _ _ _
  rw [e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_sub_distrib, GlobalTheory.T.block_form_curve_class_degree_sum _ _ _ Y.j_pos Y.j_lt, e3]
  ring
