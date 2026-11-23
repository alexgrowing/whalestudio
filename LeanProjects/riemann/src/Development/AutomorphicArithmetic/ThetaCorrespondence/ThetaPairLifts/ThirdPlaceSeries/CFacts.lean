import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.FactsOfPre
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisPreconditions
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleSevenRestrict
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SParts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamPointsWeightJumps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleJOfRestricted
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvG6OfAdmStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalC
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory Tr
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem pre_cut_alt {c : CutD D} (hc : c.Good) {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) : _root_.UpperTheory.GalC.GaloisPreconditions (cut D c) (nchCut c x) :=
  have R := _root_.UpperTheory.GalC.Tr.rs_cut_of_good_aux41 hc h.Conclusion1.1 h.what₂
  have A := _root_.UpperTheory.GalC.Tr.admissible_cut (c := c) h.adm
  have lam : GlobalTheory.NRows.LamUsed (cut D c) := h.lam
  { what₂ := R
    adm := A
    Conclusion1 := _root_.UpperTheory.GalS.Parts.main_alt_alt _ A.1 R.a.tieLab R.b.rowSize R.a.hecke lam.loc R.b.thetaOne R.a.g4p
    z := pointsAdmissible_restrictToPoints hc h.z
    rhoBar := rhoBar_cut h.rhoBar
    g3p := _root_.UpperTheory.GalC.Tr.admissible_tame_eigenvalues_of_cut h.g3p
    weight := fun i => h.weight i.1
    block := fun i => h.block i.1
    muUnr := fun i => h.muUnr i.1
    depthG := fun i => h.depthG i.1
    bc := h.bc
    lam := lam
    c2 := jointCondition_restrictToPoints h.c2
    large := large_cut h.large
    nct := nct_cut c h.nct
    trip := fun a => h.trip a.1
    same := fun a => h.same a.1
    good := h.good }
theorem facts_of_galois_preconditions_of_cutRec (hCh : GlobalTheory.TwSys.Cheb) (lf : LocalFiniteness) (ltd : LocalTateDuality) (lec : LocalEulerChar)
    {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) (hC : CutRec D) : _root_.GlobalTheory.NFacts.NormChoiceFacts D x :=
  have ex : GlobalTheory.StringRepresentationDecomposition.RbEx D := GlobalTheory.T.residualRankPartExists_of_jointCondition D h.what₂.c.rho
  have h0 : SumRepresentations.tie0 D := h.adm.1.1.1
  have h1 : SumRepresentations.adm1 D := h.adm.1.1.2.2.1
  have g2 := _root_.UpperTheory.GalS.de_rham_points_weight_jumps_alt D h0 h1 h.what₂.a.a2 h.what₂.a.a5 hC
  { what₂ := h.what₂, adm := h.adm, Conclusion1 := h.Conclusion1
    Conclusion2 := ⟨_root_.UpperTheory.GalS.prvG5_of_admissible_cutRec lf ltd lec D h.adm ex hC, _root_.GlobalTheory.T.prvG6_of_admissible' D h.adm ex, h.z⟩
    rhoBar := h.rhoBar, g3p := h.g3p, weight := h.weight, block := h.block, g2 := g2
    admJ := fun L hL => _root_.UpperTheory.GalS.admJ_of_admPar D L h0 h1 h.what₂.a.a2 h.what₂.a.a5 hC h.weight h.block hL
    muUnr := h.muUnr, depthG := h.depthG, bc := h.bc, lam := h.lam, c2 := h.c2, large := h.large
    duties := _root_.UpperTheory.GalS.duties_of_large_aux41 hCh D h.large h.Conclusion1.1 g2.2 h.rhoBar
    nct := h.nct, trip := h.trip, same := h.same, good := h.good }
theorem exists_good_cut_facts_tie4 (hCh : GlobalTheory.TwSys.Cheb) (lf : LocalFiniteness) (ltd : LocalTateDuality) (lec : LocalEulerChar)
    {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) (hT : Tie4 D) :
    ∃ c : CutD D, c.Good ∧ _root_.GlobalTheory.NFacts.NormChoiceFacts (cut D c) (nchCut c x) ∧ Tie4 (cut D c) := by
  obtain ⟨c, hc⟩ := _root_.UpperTheory.GalC.exists_good_alt (GlobalTheory.T.central_elements_from_idempotent_coeffs GlobalTheory.CentralIdem.centralIdemCoeff) h hT
  exact ⟨c, hc, _root_.UpperTheory.GalC.facts_of_galois_preconditions_of_cutRec hCh lf ltd lec (_root_.UpperTheory.GalC.pre_cut_alt hc h) (cutRec_cut hc), compatibilityTies_eigenRestriction c hT⟩
end UpperTheory.GalC
end
end
