import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenBridge.SuppLev
end GlobalTheory.PenBridge.SuppLev
open GlobalTheory.PenBridge in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.PenBridge.supp_mem_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (P : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p ∈ P, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p ∧ ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p) → ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ P), (∀ i, (J.G i).q.v ∈ P → _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj x i ∈ KO (J.G i).k _) → x ∈ J'.A.U j (J'.ι j α') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ t' J' hJ' α' P hP x hx hrd
  have hjm : j ≤ B.R.m := by omega
  have hok : I.Ok := hW.tr.ok
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L := (ha.x j hjm).sd
  haveI : Submodule.IsLattice (I.rec7 l Z).host.E (a.g.x j).L := hsd.1
  have hfg : (a.g.x j).L.FG := Submodule.IsLattice.fg (A := (I.rec7 l Z).host.E)
  have hlb := (hJ'.is.reads j hjm).lb (J'.ι j α')
  refine (hJ'.is.U j hjm _ _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hx, ?_⟩
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hd : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := ⟨_, (hPr.piT_norm u).symm⟩
  refine GlobalTheory.PenBridge.SuppLev.exists_mem_level_set (I.rec7 l Z) _ _ _ (J'.A.K j hjm (J'.ι j α')).lev (X.piT u) hd hlb
    (a.g.x j).L hfg
    (fun y => ((hat.pinX.xs j hjm).2.2 y).trans
      (forall_congr' fun r => ⟨fun h => ⟨⟨y r, h⟩, rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.2⟩)) (· ∈ P) x hx ?_
  intro v hvP
  obtain ⟨⟨i, hi⟩, hn'⟩ := hP v hvP
  subst hi
  have hu : I.UnderQ (W.P.I.tup t) (J.G i).q.v :=
    ⟨J.pl i, (hW.tq.Q t (J.pl i)).1 (J.mem i), ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).2 i).symm⟩
  obtain ⟨hTv, hgv⟩ := GlobalTheory.Mem.Col2.TC.underQ_notMem I hok l u _ _ hu
  refine ⟨fun h => ?_, hTv, ?_⟩
  · rcases hJ'.is.bad_le j hjm _ h with (h0 | h0) | ⟨Q, hQ, e⟩
    · exact hgv 0 h0
    · exact hgv 1 h0
    · obtain ⟨i', hi'⟩ := hJ'.surj Q ((hW.tq.Q t' Q).2 hQ)
      refine hn' ⟨i', ?_⟩
      rw [(_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t' J' hJ').2 i', hi']
      exact e
  · have h1 := hrd i hvP
    rw [_root_.GlobalTheory.PenBridge.reductionHomAtLastLevel, MonoidHom.pi_apply, _root_.GlobalTheory.PenBridge.rd_at_apply, toSum0_mem_KO_iff] at h1
    exact GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J.G i).q _ hsd (_root_.GlobalTheory.PenBridge.int_in_frame_at_level J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) h1
end
end
