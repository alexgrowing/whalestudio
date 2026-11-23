import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocLeLevelPrimeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CosetLevelEqOfReadsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
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
namespace GlobalTheory.PenLevOff
section Cut
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut
set_option synthInstance.maxHeartbeats 200000
variable {D : D7}
end Cut
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}
end Level
end GlobalTheory.PenLevOff
end
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.PenLevOff.uloc_le_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' v → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hv hv'
  have hjm : j ≤ B.R.m := by omega
  by_cases hTv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · exact _root_.GlobalTheory.T.true_geometry_coset_value_alt W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hTv
  by_cases hb : v ∈ J'.A.bad j
  · rcases hJ'.is.bad_le j hjm v hb with hg | hq
    · exact _root_.GlobalTheory.T.true_geometry_coset_relation_alt W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hg hTv hv hv'
    · exfalso
      obtain ⟨P, hP, hPv⟩ := hq
      obtain ⟨i, hi⟩ := hJ'.surj P ((hW.tq.Q t' P).2 hP)
      exact hv' ⟨i, (((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha haT t' J' hJ').2 i).trans (congrArg _ hi)).trans hPv⟩
  · rw [(J'.A.K j hjm (J'.ι j α')).lev.Uloc_hyp v hb hTv]
    refine ((J.A.K j hjm (J.ι j α)).lev.Uloc_lev v).trans (le_of_eq ?_)
    congr 1
    ext z
    exact ((hJ.is.reads j hjm).lb _ z).trans ((hJ'.is.reads j hjm).lb _ z).symm
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.PenLevOff.cut_mem_U_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p → p ∈ Q) → (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p → p ∈ Q) → ∀ x ∈ J.A.U j (J.ι j α), GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj t J hJ α t' J' hJ' α' Q hQ hQ' x hx
  have hjm : j ≤ B.R.m := by omega
  have hxG : x ∈ GfC _ := ((hJ.is.U j hjm _ x).1 hx).1
  have h1 := GlobalTheory.FinPl.SetCut.cutG_mem_Q _ Q x
  have h2 := GlobalTheory.FinPl.SetCut.cutG_mem_Qc _ Q hxG
  have e := GlobalTheory.FinPl.SetCut.cutG_mul_cutG _ Q x
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.idemQ_mul_self Q) x = g₁ at h1 e
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x = g₂ at h2 e ⊢
  refine (GlobalTheory.PenLevOff.mem_U_iff hJ'.is j hjm _ g₂).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h2, fun v => ?_⟩
  by_cases hv : v ∈ Q
  · rw [GlobalTheory.PenLevOff.cutAt_eq_one _ (P := (· ∉ Q)) (not_not.2 hv) h2]
    exact one_mem _
  · have h4 := ((GlobalTheory.PenLevOff.mem_U_iff hJ.is j hjm _ x).1 hx).2 v
    rw [← e, map_mul, GlobalTheory.PenLevOff.cutAt_eq_one _ (P := (· ∈ Q)) hv h1, one_mul] at h4
    exact GlobalTheory.PenLevOff.mem_of_uloc_le hJ.is hJ'.is j hjm _ _ v
      (_root_.GlobalTheory.PenLevOff.uloc_le_alt W hW u a ha haT j hj t J hJ α t' J' hJ' α' v (fun h => hv (hQ v h)) (fun h => hv (hQ' v h)))
      (GlobalTheory.PenLevOff.cutAt_mem _ v _) h4
end
