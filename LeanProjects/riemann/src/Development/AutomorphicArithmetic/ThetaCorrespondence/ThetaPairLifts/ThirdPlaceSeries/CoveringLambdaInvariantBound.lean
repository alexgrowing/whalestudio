import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringLambdaInvariantBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntegralCuspSlopePowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZStatement

set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.LamAll
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem covering_lambda_all_places_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftLambdaBound := by
  intro hP hG hM
  have hc := _root_.UpperTheory.Lit.Tam.integral_cusp_slope_power_bound_alt_alt hP hG
  have hH : _root_.GlobalTheory.CovTop.HostNAlt 1 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 1
  have hW : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.T.lift_weight_numerator
  refine Closed.imp ((((hc.and hM).and hH).and hG).and hW) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨⟨⟨⟨A1, hA1, hc⟩, ⟨Cm, hCm, hm⟩⟩, ⟨Ah, hAh, hh⟩⟩, ⟨Cg, -, hg⟩⟩, ⟨Cw, -, hw⟩⟩ := h
  refine ⟨A1 + (Ah + 1) + (⌈2 * Cm⌉₊ : ℝ), by have := Nat.cast_nonneg (α := ℝ) ⌈2 * Cm⌉₊; linarith, ?_⟩
  obtain ⟨x0, H⟩ := (((hc.and hm).and hh).and hg).and hw
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := H x hx hle ι p hp
  have hH1 := c i
  have hX : 10 ≤ (Fm.L x ι).sc.x := hH1.big.2.1.trans hH1.big.2.2.1
  have hb : 0 ≤ (Fm.L x ι).sc.b := le_trans (by positivity) hH1.room
  exact le_rpow_of_add hX hb hA1 (by linarith [hH1.poly.1]) hCm (unitE_le p i hH1 (e i))
    ((slopeMax_all_le p i Cm (d i) (b i)).trans (by linarith [a i]))
end GlobalTheory.CovTop.LamAll
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLambdaBound_of_gram_meas : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftLambdaBound := by
  first | exact @_root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places_alt | exact _root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places_alt | (intros; apply _root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places_alt <;> assumption)
end
end
