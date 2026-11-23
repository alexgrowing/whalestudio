import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfMeanBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortOfInputs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarryingSectionIntegralFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarryingSectionOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepStOfSrcSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SourceStatementOfSlopeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeStatementOfInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InputsOfScholzeWeinsteinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfDeepGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovHtAll

theorem height_of_steps : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    HypothesesY → Hypotheses2 → HypothesesH → Known₂ → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.ScholzeWeinsteinB → DeepGood → Size → Deg → FlatDeg → Height := by
  intro pxh gd hq py p2 ph q hks hsl hsw dg sz dd fd
  have px : GlobalTheory.CovTop.HypothesesX := pxh.toClassicalTheoremsX
  have hShort : Short := GlobalTheory.CovHt.ShortPf.short p2 dg sz fd
  have hGeom : Geom := GlobalTheory.T.geometric_of_published_inputs px gd hq p2 ph.sieg hks hsl dg sz
  have hMult : MultC := GlobalTheory.CovMult.multC_of_refW (GlobalTheory.RefSum.refW_of_size p2 dg sz fd) (GlobalTheory.T.exists_carrying_section_orders p2 ph dg sz fd)
  have hBudget : Budget := GlobalTheory.CovHt.BudgetPf.budget GlobalTheory.CovTop.Sizes.hostN GlobalTheory.CovTop.WtShape.wtN sz
  have hSlope : SlopeSt := GlobalTheory.T.slope_statement_of_inputs pxh py p2 ph (GlobalTheory.T.inputs_of_scholze_weinstein pxh p2 ph q hsw)
  have hDeep : DeepSt := GlobalTheory.CovHt.DeepOfSrc.deepSt_of_srcSt p2 ph (GlobalTheory.T.source_statement_of_slope pxh p2 ph q.reg hSlope)
  refine GlobalTheory.T.height_of_mean_bound px p2 dg sz dd hShort hGeom hMult hBudget ?_
  obtain ⟨C, hC, h⟩ := hDeep
  refine ⟨C, hC, fun D T hT hm => ?_⟩
  first | exact h D T hT | exact h D T hT hm

end GlobalTheory.CovHtAll
