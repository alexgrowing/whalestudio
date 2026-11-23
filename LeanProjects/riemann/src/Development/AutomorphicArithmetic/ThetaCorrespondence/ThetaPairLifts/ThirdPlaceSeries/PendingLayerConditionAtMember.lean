import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsAOfJumpCountStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DepthZeroEigenSpanAdmissibleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemAnd
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZlStableAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpsCardOfBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedConditionOfLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SClose
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftSplitsLocally
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerSide
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem tieChi_of_labAll_green_chi_cen (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hS : GlobalTheory.Published.DepthZeroSupport) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (hX : GlobalTheory.NJoin.Agree X P.M P.rep) (hJ : JumpsCard D.nd D.naut)
    (hlab : GlobalTheory.PendOf.LabAll D P.T) (hgreen : GlobalTheory.PendOf.GreenLab P.ty.grp) (hchi : ChiTOk D P.cf)
    (hcen : CenLoc D P.M) (hzl : GlobalTheory.PendOf.ZLStable D) (hci : GlobalTheory.PendOf.CenInt D) (hroots : RootsLL D) :
    PairedCharacterCondition.tieChi (D := D) ∧ ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  have hrow : ∀ i : D.nd.Loc, Nonempty (GlobalTheory.NPin.RowMod D P.rep (D.nd.j i)) := by
    intro i
    have h1 := (D.nd.j_range i).1
    have h2 := (D.nd.j_range i).2
    obtain ⟨Y, -⟩ := _root_.GlobalTheory.RowModCanon.main_alt_alt hP.hc hP.decay hL D P X hX ⟨D.nd.j i - 1, by omega⟩ (D.nd.j i) (by simp; omega)
    exact ⟨Y⟩
  have hA := _root_.UpperTheory.GalS.a_close_main hP.what₂ hL D P hJ
  have hZ := GlobalTheory.ZetaSer.rootsOfUnity_and_seriesIdempotent_rational D hroots
  exact ⟨_root_.GlobalTheory.TieChiPin.locComp_of_isRc_classMapD_cenLoc hP.what₂ hL D P hrow hlab hchi,
    _root_.GlobalTheory.PinClose.locComp_of_isRc_classMapD_cenLoc hP.what₂ hS hL D P hrow hlab hcen hgreen hchi hA.tie0 hA.a5 hzl hci (hZ.2 P.ty.grp) hZ.1⟩
theorem locComp_of_isRc_classMapD_cenLoc : HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hH hP hS hL
  have h1 := _root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.T.cenLoc_zlStable_cenInt_at_members hL) (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_at_members_of_htCard hH hL)
    (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt hP hL) (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_mono_of_colPin (hL := hL) GlobalTheory.HeightCounting.Up.sizes_host_at_record)))
  refine _root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_mono h1 fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨hcen, hzl, hci⟩, hJ, ⟨X, hpin, -⟩, -, -, hroots, -⟩ := h
  have hM : X.P.M = c.a.all.gal.mt := hpin.M_eq
  exact _root_.GlobalTheory.HeightCounting.Up.PendLayer.tieChi_of_labAll_green_chi_cen hP hS (w.D Z) X.P X.X X.agree hJ hpin.lab hpin.green hpin.chiT (hM ▸ hcen) hzl hci hroots
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieChi_at_mem_of_depth_zero_inputs : (HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
