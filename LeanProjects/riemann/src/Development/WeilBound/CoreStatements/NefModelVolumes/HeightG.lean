import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarryingSectionOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarryingSectionIntegralFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortOfInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeightStatement
import Development.WeilBound.CoreStatements.NefModelVolumes.TwoLtHalfFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfDeepGoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
open GlobalTheory.CovTop GlobalTheory.BigTop

namespace SelfIntersectionVolumeEstimates

set_option maxHeartbeats 1000000 in

theorem heightG : SelfIntersectionVolumeEstimates.VolInputs → GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → DeepGood → Size → Deg → FlatDeg → Height :=
  fun hSB hX hGD hQ hP hH hD hG hS hDg hF => GlobalTheory.CovHt.HtTopG.height_of_steps hSB hP hG hS hDg (GlobalTheory.T.short_of_inputs hP hG hS hF) (GlobalTheory.T.geometric_of_published_inputs hX hGD hQ hP hH.sieg hX.ks hX.lie hG hS) (GlobalTheory.T.carrying_section_integral_frame (GlobalTheory.T.reference_weight_of_deep_good hP hG hS hF) (GlobalTheory.T.exists_carrying_section_orders hP hH hG hS hF)) (GlobalTheory.T.budget_of_size_and_weight GlobalTheory.T.host_bound_holds GlobalTheory.T.weight_bound_holds hS) hD

end SelfIntersectionVolumeEstimates
