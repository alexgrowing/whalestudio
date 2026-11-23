import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalQuadraticRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ThetaRR

theorem gdeg_det_rank_zero : ∀ (HC : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (hp : IsArithVar p 1) {E : X.Modules} {h : VMetric p E 0} (H : h.IsCInf), gdeg (VMetric.det H) 1 = 0 := by
  intro HC k _ X _ p hp E h H
  have hφ : ∀ σ c y, ((VMetric.det H).φ σ).φ c y = 0 := by
    intro σ c y
    show -Real.log ((h.met σ).G c y).det.re = 0
    simp [Matrix.det_isEmpty]
  have hd : ∀ σ (c : AlgChart p σ 1) y, c.chernDens ((VMetric.det H).φ σ) y = 0 := by
    intro σ c y
    simp only [AlgChart.chernDens, AlgChart.hess, hφ]
    have h0 : ReciprocityTheory.L2DbarEstimates.cHess 1 (fun _ => ((0 : ℝ) : ℂ)) (c.e y) = 0 := by
      have hw : ∀ b : Fin 1, ReciprocityTheory.L2DbarEstimates.wdb 1 b (fun _ => ((0 : ℝ) : ℂ)) = fun _ => 0 := by
        intro b
        funext v
        simp [ReciprocityTheory.L2DbarEstimates.wdb]
      ext a b
      simp only [ReciprocityTheory.L2DbarEstimates.cHess, Matrix.of_apply, hw]
      simp [ReciprocityTheory.L2DbarEstimates.wd]
    rw [h0]
    simp
  have hm : ∀ σ (ε : ℤˣ), ((VMetric.det H).φ σ).chernPart 1 ε = 0 := by
    intro σ ε
    simp only [Weight.chernPart, hd, mul_zero, ENNReal.ofReal_zero]
    have hz : ∀ g : ReciprocityTheory.L2DbarEstimates.V 1 → CxPts p σ, (fun _ : CxPts p σ => (0 : ENNReal)) ∘ g = 0 :=
      fun _ => rfl
    simp only [ChartGlue.glueMeas, ChartGlue.chartMeas, hz, MeasureTheory.withDensity_zero,
      MeasureTheory.Measure.map_zero]
    exact le_antisymm (iSup_le fun _ => le_rfl) (MeasureTheory.Measure.zero_le _)
  simp [gdeg, chInt, Weight.chernInt, hm]

end GlobalTheory.ThetaRR
