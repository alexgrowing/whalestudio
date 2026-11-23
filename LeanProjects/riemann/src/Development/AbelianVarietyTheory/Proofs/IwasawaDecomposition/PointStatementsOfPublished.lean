import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Formalism.SharpRestriction.LevelLetterCocycles.ResidualIrreducibleOfTheoremThreePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisSide
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisTer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsOfInputsAndJumpsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigISupEqTopOfSep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtInputOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrredOfCharpolyEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleAndLamUsedAllStatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInputsAllStatesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Up

namespace PointStatements

section Loc

variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}

theorem built_anti {big big' : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)} (h : ∀ w, big' w ⊆ big w)
    (hb : GlobalTheory.CoefDuty.Built A M C tup big L) : GlobalTheory.CoefDuty.Built A M C tup big' L := by
  obtain ⟨Sp, hA, hs⟩ := hb
  exact ⟨{ Sp with iq_big := fun i z hz => Sp.iq_big i z (h _ hz) }, hA, hs⟩

theorem evO_mono_loc {P Q : D7 → Prop} (h : ∀ L : LocAll (lay0 D), P (withLoc L) → Q (withLoc L))
    (hP : GlobalTheory.CoefDuty.EvO A M C tup P) : GlobalTheory.CoefDuty.EvO A M C tup Q :=
  let ⟨b, hb⟩ := hP; ⟨b, fun L hL => h L (hb L hL)⟩

theorem evO_and {P Q : D7 → Prop} (hP : GlobalTheory.CoefDuty.EvO A M C tup P) (hQ : GlobalTheory.CoefDuty.EvO A M C tup Q) :
    GlobalTheory.CoefDuty.EvO A M C tup fun D' => P D' ∧ Q D' := by
  classical
  obtain ⟨b1, h1⟩ := hP
  obtain ⟨b2, h2⟩ := hQ
  exact ⟨fun w => b1 w ∪ b2 w, fun L hL => ⟨h1 L (built_anti (fun w => Finset.subset_union_left) hL),
    h2 L (built_anti (fun w => Finset.subset_union_right) hL)⟩⟩

end Loc

theorem allSt_mono {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) (hp : AllSt p) : AllSt q :=
  hp.trans (StepW.of_all fun _ _ _ _ _ _ _ H P x => h _ _ _ _ _ P x (H P x))

theorem allSt_and {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (hp : AllSt p) (hq : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  (StepW.and hp hq).trans (StepW.of_all fun _ _ _ _ _ _ _ H P x => ⟨H.1 P x, H.2 P x⟩)

theorem rhoBar_of_rows (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7)
    (I : GlobalTheory.NRows.Inputs hL D) (R : GlobalTheory.NRows.Rows D) : AutomorphicSideWildInertia.ResidualIrreducibleGood D :=
  Formalism.MainNotions.AdmissibleThreePrime.residual_irreducible_of_theorem_three_prime D
    ⟨R.a.tieLab, GlobalTheory.AdmTame.main D R.a.tie0 R.a.a2 R.a.a5 (GlobalTheory.TieLabAt.main hL D I.P).2.1⟩
    R.a.a5 (GlobalTheory.BrauerNesbittIrr.litBNIrr _) R.c.rho R.c.dz

theorem galois_statements_at_of_inputs {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (hPr : GlobalTheory.NRows.Hypotheses₂) (hc : GlobalTheory.Published.HarishChandraFinite)
    (dec : GlobalTheory.Published.CuspRapidDecay) (I : GlobalTheory.NRows.Inputs hL D) (hJ : JumpsCard D.nd D.naut) :
    SumRepresentations.Conclusion41 D ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D ∧ SumRepresentations.Conclusion42 D ∧ SumRepresentations.ConclusionZ D := by
  have R : GlobalTheory.NRows.Rows D := GlobalTheory.T.rows_of_inputs_and_jumps hPr hc dec hL D I hJ
  have h1 : SumRepresentations.Conclusion1 D := I.Conclusion1 (GlobalTheory.T.parts_give_dimension D) R.a R.b
  exact ⟨h1.1, rhoBar_of_rows hL D I R, h1.2.2, (SumRepresentations.multiplicity_statement_iff_reduced D I.isot h1.2.2).2 (GlobalTheory.T.reduced_form_of_local_inputs hL D I R)⟩

end PointStatements

open PointStatements in

theorem pointStatements_of_hypotheses : PrN → GlobalTheory.NRows.HypothesesX → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PtSt hL := by
  intro hP hX hL
  have h := allSt_and (allSt_and (allSt_and (GlobalTheory.T.coefficient_duty_inputs_all_states hL hP hX) (GlobalTheory.HeightCounting.JumpsSt.main hL hP hX.ht))
    (GlobalTheory.HeightCounting.Up.ptSt_eigSpan hL hP)) (GlobalTheory.T.admissible_and_lam_used_all_states hP hX)
  refine allSt_mono (fun K B f T w P x H l => ?_) h
  obtain ⟨⟨⟨hI, hJ⟩, hE⟩, hS⟩ := H
  refine evO_mono_loc ?_ (evO_and (evO_and (hI l) (hJ l)) (hE l))
  rintro L ⟨⟨hI', hJ'⟩, hE'⟩
  exact ⟨fun ho => galois_statements_at_of_inputs hP.what₂ hP.hc hP.decay (hI' ho).some (hJ' ho), hE', hS.1⟩

end GlobalTheory.HeightCounting.Up

end
