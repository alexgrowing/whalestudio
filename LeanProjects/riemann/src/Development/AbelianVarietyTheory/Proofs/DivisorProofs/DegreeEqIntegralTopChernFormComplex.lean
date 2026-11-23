import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionDivisorEqSelfIntersectionPresentedStatement

namespace GlobalTheory.ChernDegree

theorem chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex := fun Y Δ L r hr φ hφ =>
  ⟨(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).1, by
    rw [GlobalTheory.T.chernMass_eq_selfIntersection_lineBundle Y L φ hφ, GlobalTheory.T.intersection_divisor_eq_selfIntersection_presented Y Δ L r φ.isLB hr]⟩

end GlobalTheory.ChernDegree
