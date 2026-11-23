import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IoYStOfIoPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsLevelCharacterConditionsHoldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChainStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.ExIoY

theorem ex_ioY_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW → R.ex_ioY := by
  intro hDS hHC hCR hCW D G _ _ Pl0 T A Ks _ _ _ R hL hF hM hH hW
  have hθ : IsInfFam R.θ := hM.inf
  have hE : R.ex_ItY := GlobalTheory.T.exists_innerStepIntertwiners_thetaChain hDS hHC D G Pl0 T A Ks R hL hF hM hH hW
  have hI : R.chain_ItY := fun t k hk => (hW.ItY k hk).1 (hE k hk) t
  have hS : GlobalTheory.Chain.StepsOK R :=
    GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX
  have hLw : GlobalTheory.Chain.LawsOK R := GlobalTheory.T.chainSteps_levelCharacter_conditions_hold D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX
  have hY := GlobalTheory.Chain.ioYSt_of_ioPair D G Pl0 T A Ks R (GlobalTheory.T.exists_thetaLift_multiplicitySpaces_of_hypotheses hDS hHC hCR hCW D)
    (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hθ hS hLw hM.νY hM.νY' hI
  exact fun t k hk => hY t k hk

end GlobalTheory.Chain.ExIoY
