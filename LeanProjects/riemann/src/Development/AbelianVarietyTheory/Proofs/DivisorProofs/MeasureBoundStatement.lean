import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfOneMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMeasureOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioUpperBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioLowerBoundStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

namespace GlobalTheory.CovTop.MeasRd

theorem meas : Hypotheses2 → Meas := by
  intro h
  have h2 := GlobalTheory.T.one_measure_of_classicalTheorems h
  refine Closed.imp (Closed.and (GlobalTheory.T.log_ratio_upper_bound h2) (GlobalTheory.T.log_ratio_lower_bound h)) ?_
  intro _ Fm _ _ hh
  obtain ⟨⟨K1, hK1, a, ha⟩, ⟨K2, hK2, b, hb⟩⟩ := hh
  refine ⟨(K1 + K2) / 2, by positivity, max a b, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨hr, hu⟩ := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hl := hb x hx ((le_max_right _ _).trans hle) ι p hp i
  exact measAt_of p i (GlobalTheory.T.exact_at_of_one_measure p hp.1 (h2 _) i) hr hK1 hK2 hu hl

end GlobalTheory.CovTop.MeasRd

end
