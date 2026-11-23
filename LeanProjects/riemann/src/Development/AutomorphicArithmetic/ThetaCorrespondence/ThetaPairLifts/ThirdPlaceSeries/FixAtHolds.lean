import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjTwOfOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
open GlobalTheory.ConjTwist
theorem fixAt_holds_alt : GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition := by
  intro hRF hA
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt) fun Fm x hx k p hr hm w _ j H => ?_
  intro ρ hρ hp hL τ hτ
  have hR := _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx k p hr hm _ H.1.2.2 H.2 j
  have hτ' : ∀ z ∈ (Formalism.L2.Host.embLL0 (Fm.D x k)).fieldRange, τ z = z := by
    rintro _ ⟨y, rfl⟩
    exact hτ y
  have hFB : FixBase p.T p.R.toRealDat j τ :=
    GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField _ _ _ _ _ _ hRF p.T p.R p.cG p.Sx p.nexp (F2 p) p.κ p.v₀ hR.laws hR.core hR.fw hR.tieIn hR.galois
      hR.small.val hR.small.ray hR.small.roots j τ hτ'
  refine ⟨hFB, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := de_chi_eq hρ ((Fm.ex x hx k).nch.twI w) j ((Fm.ex x hx k).nch.sd w) y
    change τ (((ρ.B _ j _).de.chi y : Circle) : ℂ) = _
    rw [hσ]
    refine GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values ρ hρ _ j _ (p.R.C.delAt ((Fm.D x k).ntw.l ((Fm.ex x hx k).nch.twI w))) (hp.delta _ j _) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [hR.small.val.del', hR.small.val.del]
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := (ρ.eG ((Fm.ex x hx k).nch.twI w) j ((Fm.ex x hx k).nch.sd w)).surjective q
    obtain ⟨g, rfl⟩ := (p.R.eG.trans p.cG).surjective y
    have hg := (mem_level_iff hm.2.2 hL _ j _ g).1 hq
    obtain ⟨z, hz⟩ := (level_chi hm.2.2 hρ hL _ j _ ⟨g, hg⟩ hq).2
    change τ ((((ρ.B _ j _).G.P.chi ⟨_, hq⟩ : ℂˣ) : ℂ)) = _
    rw [← hz]
    exact hτ z
  · exact (baseOf_of_realPin hR.core.lev hρ hp _ j _).fix_mu hR.core.lev (hρ.base _ j _) hFB.chi
end GlobalTheory.BigOn.Exp.TwConj
end
end
