import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsLevelCharacterConditionsHold
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainSteps_levelCharacter_conditions_hold : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → LawsOK R := by
  first | exact @GlobalTheory.Chain.SourceLaw.lawsOK | exact GlobalTheory.Chain.SourceLaw.lawsOK | (intros; apply GlobalTheory.Chain.SourceLaw.lawsOK <;> assumption)
