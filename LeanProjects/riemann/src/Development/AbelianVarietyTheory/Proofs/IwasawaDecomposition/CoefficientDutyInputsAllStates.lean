import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMono
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroOfHoweUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyTiedAllStatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointCondThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeDefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleAndLamUsedAllStatesStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtInputsX

theorem inputs_at_third : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX →
    AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x,
    GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (GlobalTheory.NRows.Inputs hL D') := by
  intro hL hP hX
  have h := (((GlobalTheory.T.coefficient_duty_tied_all_states hL hP hX).and (GlobalTheory.HeightCounting.Up.JointConditionThird.jointCond_third hL hP)).and
    (GlobalTheory.T.base_change_definite_unitary hL hP)).and ((GlobalTheory.T.admissible_and_lam_used_all_states hP hX).and (GlobalTheory.T.series_local_of_hypothesis hL hP))
  refine h.trans (StepW.of_all fun K B f T w _ _ hh P x l => ?_)
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h45, h6⟩ := hh
  have h4 : GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.NRows.LamUsed D' :=
    ⟨fun _ => ∅, fun _ _ _ => (h45 P x).2⟩
  have h5 : GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SumRepresentations.adm8 D' :=
    ⟨fun _ => ∅, fun _ _ _ => (h45 P x).1⟩
  have e := fun (P₁ P₂ : D7 → Prop) => GlobalTheory.CoefDuty.LargeRing.evO_laws _ _ _ l.a.A l.mt.M l.c.ch l.c.tp.tup P₁ P₂
  have a := (e _ _).1 (h1 P x l) ((e _ _).1 (h2 P x l) ((e _ _).1 (h3 P x l) ((e _ _).1 h4
    ((e _ _).1 h5 (h6 P x l)))))
  refine (e _ _).2.1 (fun D' hD' hO => ?_) a
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hD'
  obtain ⟨T⟩ := t1 hO
  exact ⟨⟨T, ⟨hO, t2 hO, t3 hO, t4 hO, t5 hO, t6 hO,
    GlobalTheory.T.type_nonzero_of_howe_unramified hP.decay hP.howe hX D' T.P.cf T.P.C T.P.tp T.X⟩⟩⟩

end GlobalTheory.PtInputsX
