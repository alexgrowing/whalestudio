import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelThetaSeriesSpanOverClassRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaKernelSeriesUniqueStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem maxSt : MaxSt := by
  refine Formalism.MainNotions.Closed.of_all fun Fm _ => ⟨0, fun x hx _ i p hR hM v hv j => ?_⟩
  have hL := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC := hL.1
  have hv' : v ∈ (R2 p).twPl := hv
  have hdel : ∀ y, ((((R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 y : ℂˣ) : ℂ) ∈ (Fm.D x i).what₂.embLL.range := fun y => by
    obtain ⟨z, hz⟩ := FO_le _ (hM.2.1.delAt_mem (Formalism.EigenvalueLevelCeiling.plc v) y)
    exact ⟨z, hz⟩
  exact GlobalTheory.TraceClassRank.spanOverClasses_of
    (GlobalTheory.T.baseThetaKernel_series_unique _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j v hv' hC.tup.mu_on)
    (GlobalTheory.T.kernel_thetaSeries_span_over_class_representatives _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j v hv' hC.tup.mu_on hdel
      _ _ _)

end GlobalTheory.BigOn
