import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
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
theorem _root_.GlobalTheory.T.exists_adm_eq_thetaIntegral_of_conv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y)
    (ψ : AddChar (AF F) ℂ) (χX χY : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : Rep σ X Y), M.IsWeil ψ χX χY om →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), M.Conv om Φ) →
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 := by
  first | exact @GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral | exact GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral | (intros; apply GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral <;> assumption)
