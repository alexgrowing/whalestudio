import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjTupleAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjTwOfOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLevAtHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
open Classical in
theorem tupAt_alt (h1 : GlobalTheory.Published.CuspRapidDecay) (h2 : GlobalTheory.Published.GlobalArtinReciprocity) (h3 : GlobalTheory.Published.RayClassFieldSt)
    (h4 : GlobalTheory.Published.DiscreteSeriesCover) (h5 : GlobalTheory.Published.CasselmanWallach) (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hC : _root_.GlobalTheory.BigOn.Exp.TwistCharacter) : _root_.GlobalTheory.BigOn.Exp.TwConj.TupleCondition := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt) (_root_.GlobalTheory.BigOn.Exp.TwConj.twLevAt_holds_alt h1 h2 h3 hA hC)) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨hadm, hlow⟩, hlev⟩ := H
  intro ρ ρ' hρ hρ' hp hS hAd
  have H0 := _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hr hm _ hadm.2.2 hlow j
  have hB : BaseOf p.R.toRealDat j (baseW (Fm.ex x hx i) w j ρ) := baseOf_of_realPin H0.core.lev hρ hp _ j _
  have hLaws : Laws p.T p.R.toRealDat (F2 p) p.κ p.v₀ p.O (phs p) j (baseW (Fm.ex x hx i) w j ρ) :=
    ⟨H0.core, H0.fin, H0.fw, H0.io, H0.guard, H0.pins, H0.phase, hB⟩
  obtain ⟨χ, χ', xiR, xiR', hT, hT', hne, hne', hd⟩ := hlev ρ ρ' hρ hρ' hp hS hAd
  obtain ⟨A0, R0, F0, v0, O0, hL0, hE0, hxi0, htr⟩ := GlobalTheory.BaseRestrict.restrict_to_base _ _ _ _ _ _ _ _ _ hLaws
  have hT0 := htr _ _ _ _ hT
  have hT0' := htr _ _ _ _ hT'
  have hQ : (twW (Fm.ex x hx i) w ρ').Q = (twW (Fm.ex x hx i) w ρ).Q := by simp only [Setup.tw, twistOf, hS.2.1]
  have hQde : ∀ (N : Type) (Qn : N → Finset (Pl (Fm.D x i).host.E)),
      (∀ n, Qn n = (baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q) →
      ∀ q ∈ ({(Fm.D x i).host.pde, (Fm.D x i).host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 (Fm.D x i).host.K),
        (∀ t, ∀ PP ∈ R0.Q t, ((q : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ PP.asIdeal → PP.under (𝓞 (Fm.D x i).host.K) = 𝔭) ∧
          ∀ n, ∀ PP ∈ Qn n, ((q : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ PP.asIdeal → PP.under (𝓞 (Fm.D x i).host.K) = 𝔭 := by
    intro N Qn hQn q hq
    obtain ⟨𝔭, h𝔭, h𝔭'⟩ := hT0.Q_de q hq
    exact ⟨𝔭, h𝔭, fun n => (hQn n).symm ▸ h𝔭'⟩
  rcases hd with hd | hd
  · obtain ⟨T', A', R', F', v', O', hL', hE', htup⟩ := GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws h1 h2 h3 h4 h5 p.T R0 F0 p.κ v0 O0 (phs p) j _ p.host hL0 Bool
      (fun b => if b then χ' else χ)
      (fun b => if b then (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi
        else (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi)
      (fun b => if b then (baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ').Q
        else (baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q)
      (fun b => if b then xiR' else xiR)
      (fun b => by cases b <;> assumption)
      (fun a b hab => by
        cases a <;> cases b
        · rfl
        · exact absurd hab hd
        · exact absurd hab.symm hd
        · rfl)
      (fun b t => by rw [hxi0]; cases b; exacts [hne, hne'])
      (hQde Bool _ fun b => by cases b <;> simp [hQ])
    obtain ⟨t, ht1, ht2⟩ := htup false
    obtain ⟨t', ht1', ht2'⟩ := htup true
    exact hasTuples_of_laws hL' (hE0.trans hE') (t := t) (t' := t') ⟨ht1, ht2⟩ ⟨ht1', ht2'⟩
  · obtain ⟨T', A', R', F', v', O', hL', hE', htup⟩ := GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws h1 h2 h3 h4 h5 p.T R0 F0 p.κ v0 O0 (phs p) j _ p.host hL0 Unit
      (fun _ => χ) (fun _ => (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi)
      (fun _ => (baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q) (fun _ => xiR)
      (fun _ => hT0) (fun _ _ _ => rfl) (fun _ t => by rw [hxi0]; exact hne) (hQde Unit _ fun _ => rfl)
    obtain ⟨t, ht1, ht2⟩ := htup ()
    exact hasTuples_of_laws hL' (hE0.trans hE') (t := t) (t' := t) ⟨ht1, ht2⟩ ⟨ht1.trans hd, ht2.trans (by rw [hQ])⟩
end GlobalTheory.BigOn.Exp.TwConj
end
end
