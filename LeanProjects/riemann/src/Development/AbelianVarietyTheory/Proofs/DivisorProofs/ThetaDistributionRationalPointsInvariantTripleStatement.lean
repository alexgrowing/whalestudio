import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionRationalPointsInvariantTriple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_distribution_rational_points_invariant_triple : ∀ {D : D7} {a a' : ℕ} (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ γ ∈ ratU D.sp.cm.sig Γ.V.J, ∀ γ' ∈ ratU D.sp.cm.sig Γ.W.J, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin a × Fin (a + a')),
      GlobalTheory.WeilM.thetaSum D.host.F (om (γ, γ') Φ) = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  first | exact @GlobalTheory.RatInvTheta.thetaSum_rat_inv | exact GlobalTheory.RatInvTheta.thetaSum_rat_inv | (intros; apply GlobalTheory.RatInvTheta.thetaSum_rat_inv <;> assumption)
