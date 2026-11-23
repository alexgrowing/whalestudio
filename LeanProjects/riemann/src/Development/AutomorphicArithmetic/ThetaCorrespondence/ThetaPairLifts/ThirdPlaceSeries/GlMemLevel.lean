import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
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
noncomputable section
namespace GlobalTheory.LevProd.OffTwist
set_option maxHeartbeats 2000000 in
theorem gl_mem_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t₂ (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂), J₂.Reads → ∀ i : Fin J₂.r, ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J (J₂.G i).q.v → ∀ (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr = ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))).β * y.val * ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))).γ) → ∀ y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j), gl y ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α t₂ J₂ hJ₂ i hv gl hgl y hy
  have hjm : j ≤ B.R.m := by omega
  have hok : I.Ok := hW.tr.ok
  have hsup : gl y ∈ GlobalTheory.FinPl.grpAt _ (· = (J₂.G i).q.v) :=
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ (J₂.G i).q _ _ (hgl y).1 _ rfl
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L := (ha.x j hjm).sd
  have hKO : GlobalTheory.LevIdx.locHom (J₂.G i).q _ ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))) (gl y) ∈ KO _ _ :=
    (GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgl y).2 ▸ hy
  have hm := GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J₂.G i).q _ hsd ((J₂.G i).latX j _) hKO
  haveI : Submodule.IsLattice (I.rec7 l Z).host.E (a.g.x j).L := hsd.1
  have hfg : (a.g.x j).L.FG := Submodule.IsLattice.fg (A := (I.rec7 l Z).host.E)
  have hu₂ : I.UnderQ (W.P.I.tup t₂) (J₂.G i).q.v :=
    ⟨J₂.pl i, (hW.tq.Q t₂ (J₂.pl i)).1 (J₂.mem i), ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t₂ J₂ hJ₂).2 i).symm⟩
  obtain ⟨hTv, hgv⟩ := GlobalTheory.Mem.Col2.TC.underQ_notMem I hok l u _ _ hu₂
  have hbad : (J₂.G i).q.v ∉ J.A.bad j := fun h => by
    rcases hJ.is.bad_le j hjm _ h with (h0 | h0) | ⟨P, hP, e⟩
    · exact hgv 0 h0
    · exact hgv 1 h0
    · obtain ⟨i', hi'⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
      refine hv ⟨i', ?_⟩
      rw [(_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).2 i', hi']
      exact e
  have hlb := (hJ.is.reads j hjm).lb (J.ι j α)
  refine (hJ.is.U j hjm _ _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hsup, ?_⟩
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hd : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := ⟨_, (hPr.piT_norm u).symm⟩
  exact exists_mem_level (I.rec7 l Z) _ _ _ (J.A.K j hjm (J.ι j α)).lev (X.piT u) hd hlb (a.g.x j).L hfg
    (fun x => ((hat.pinX.xs j hjm).2.2 x).trans
      (forall_congr' fun r => ⟨fun h => ⟨⟨x r, h⟩, rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.2⟩)) _ hbad hTv _ hsup hm
end GlobalTheory.LevProd.OffTwist
end
end
