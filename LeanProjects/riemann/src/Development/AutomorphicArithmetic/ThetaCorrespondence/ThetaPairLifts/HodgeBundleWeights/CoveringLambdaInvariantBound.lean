import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaBoundFromMeasure
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralCuspSlopePowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TamagawaPeterssonLambdaSqNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaBoundFromMeasureStatement

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.LamAll
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem covering_lambda_all_places : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram → Meas → abelian₂ := by
  intro hP hG hM
  have hc := _root_.UpperTheory.Lit.Tam.integral_cusp_slope_power_bound_alt hP hG
  have hH : HostN 1 := GlobalTheory.CovTop.Sizes.hostN 1
  have hW : WtN := GlobalTheory.T.weight_bound_holds
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
theorem _root_.GlobalTheory.T.covering_lambda_invariant_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram → Meas → abelian₂ := by
  first | exact @_root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places | exact _root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places | (intros; apply _root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places <;> assumption)
end
