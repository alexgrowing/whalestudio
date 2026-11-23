import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResInt
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import GroundTheory.HeightsAndTheta.Heights.Intersections.StResExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem extC_map_rat_eq_map_complex {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.extC (P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
      P.map (MvPolynomial.map (Int.castRingHom ℂ)) := by
  have hc : (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MvPolynomial (Σ k, ι k) ℂ) :=
    RingHom.ext GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.map_rat_complex
  simp only [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.extC, ReciprocityTheory.AnForm.R.extC, Ideal.map_map, hc]

theorem ComponentDegree.proof (h₁ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.Statement)
    (h₂ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResExists.Statement) (h₃ : ComponentResInt.Statement) :
    ComponentDegree.Statement := by
  intro K _ _ ι _ P e L W hP hL hW
  have hW' : W ∈ (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.extC
      (P.map (MvPolynomial.map (Int.castRingHom ℚ)))).minimalPrimes := by
    rw [extC_map_rat_eq_map_complex]
    exact hW
  have hV : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.IsProjVar W e :=
    GroundTheory.Heights₂.Heights.Inter.BaseChange.isProjVar_of_mem_minimalPrimes
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP) hW'
  have hR := h₂ K ι W e hV
  rw [h₃ K ι P e L W hP hL hW hR]
  exact h₁ K ι W e L hV hR fun j =>
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isSmoothMetric_of_isSmoothHerm W (L j) (hL j)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
