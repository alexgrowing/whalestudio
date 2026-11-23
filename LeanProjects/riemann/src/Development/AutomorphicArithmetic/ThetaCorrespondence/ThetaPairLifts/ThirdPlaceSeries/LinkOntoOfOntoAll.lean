import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLinkOnto
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QBaseEmptyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevChiDatYtBaseStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ComIsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnderMemSStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepXWeilVecStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaAndItStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinalityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYWeilVecStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYThetaFunIsItWStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYIntegrableAndEqStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
open GlobalTheory.ChainOnto
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem stepY_is_alt {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hf : f.RowOK) (j : ℕ) (hj : j + 1 < D.R.m) :
    (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).Is (j + 1) :=
  ⟨(_root_.GlobalTheory.T.base_chain_step_weil_datum_alt W u f hP hf j hj).1, (_root_.GlobalTheory.T.base_chain_step_weil_datum_alt W u f hP hf j hj).2, (_root_.GlobalTheory.T.base_chain_step_theta_functions_alt W u f hP hf j hj).1,
    (_root_.GlobalTheory.T.base_chain_step_theta_functions_alt W u f hP hf j hj).2, _root_.GlobalTheory.T.base_chain_step_theta_lift_alt W u f hP hf j hj⟩
theorem chainX_is_succ_succ {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hf : f.RowOK) (j : ℕ)
    (h : j + 2 * 0 + 2 = D.R.m) : (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).Is (j + 1 + 1) :=
  ⟨(_root_.GlobalTheory.T.base_chain_top_weil_datum_alt W u f hP hf j h).1, (_root_.GlobalTheory.T.base_chain_top_weil_datum_alt W u f hP hf j h).2, (_root_.GlobalTheory.T.base_chain_top_theta_functions_alt W u f hP hf j h).1,
    (_root_.GlobalTheory.T.base_chain_top_theta_functions_alt W u f hP hf j h).2, _root_.GlobalTheory.T.base_chain_top_theta_lift_alt W u f hP hf j h⟩
theorem reach_stageY_dn {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hf : f.RowOK) :
    ∀ k, k + 1 ≤ D.R.m → Reach (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0) k (_root_.GlobalTheory.BaseChain.stageOfSpaceY W k) ((f.t W.P.A3.A.μ0).dn k)
  | 0, _ => Reach.zero
  | k + 1, hk => Reach.step (reach_stageY_dn f hP hf k (by omega)) (_root_.GlobalTheory.T.baseChain_stageY_is_of_pkHyp_of_lt W hP (k + 1) (by omega)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f k)
      (_root_.GlobalTheory.BaseChain.stepY_is_alt f hP hf k (by omega))
theorem linkOnto_of_ontoAll_third_place_series : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word),
    _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.ChainOnto.OntoAll D → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkSurjective f := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP hO f hf n h T hT
  have e : 2 * n + 1 + 1 = D.R.m := by omega
  have hX : (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Is (_root_.GlobalTheory.BaseChain.com_z W) (2 * n + 1 + 1) := e ▸ _root_.GlobalTheory.T.baseChain_stageX_is_of_pkHyp W hP
  have hR := Reach.step (_root_.GlobalTheory.BaseChain.reach_stageY_dn f hP hf (2 * n + 1) (by omega)) hX (_root_.GlobalTheory.BaseChain.transitionToSpaceX f (2 * n) h) (_root_.GlobalTheory.BaseChain.chainX_is_succ_succ f hP hf (2 * n) h)
  obtain ⟨G, hG⟩ := hO hP.gap (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.T.baseChain_com_z_is_of_pkHyp W hP) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0) (_root_.GlobalTheory.T.baseChain_stageY_is_of_pkHyp_of_lt W hP 0 (by omega)) (2 * n + 1 + 1) (by omega)
    _ _ hR ⟨T, _root_.GlobalTheory.T.mem_stageY_zero_cc_of_mem_zero_set W hP T hT⟩
  exact ⟨G, congrArg Subtype.val hG⟩
end GlobalTheory.BaseChain
end
end
