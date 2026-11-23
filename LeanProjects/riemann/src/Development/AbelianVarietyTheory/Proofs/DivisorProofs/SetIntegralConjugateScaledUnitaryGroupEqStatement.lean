import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralConjugateScaledUnitaryGroupEq
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
theorem _root_.GlobalTheory.T.setIntegral_conjugate_scaled_unitaryGroup_eq : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∀ dom : Set (UB J), IsFundamentalDomain (ratU D.sp.cm.sig J) dom (ν.map (conjU V c h)) →
    ∀ f : UB J → ℂ, (∀ γ ∈ ratU D.sp.cm.sig J, ∀ x, f (γ * x) = f x) →
      ∫ u in fd, f (conjU V c h u) ∂ν = ∫ x in dom, f x ∂(ν.map (conjU V c h)) := by
  first | exact @GlobalTheory.ConjUIntegral.setIntegral_conjU_eq | exact GlobalTheory.ConjUIntegral.setIntegral_conjU_eq | (intros; apply GlobalTheory.ConjUIntegral.setIntegral_conjU_eq <;> assumption)
