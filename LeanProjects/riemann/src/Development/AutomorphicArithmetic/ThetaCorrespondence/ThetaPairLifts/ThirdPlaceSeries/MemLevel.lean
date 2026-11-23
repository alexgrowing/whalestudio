import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeConjugate
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
namespace GlobalTheory.LevProd.Bwd
section Dense
open Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.RootEx GlobalTheory.TwBridge ValuativeRel
end Dense
section Rat
open Formalism.L2.Col Formalism.UG
attribute [local instance] GlobalTheory.Mem.Col2.starE
end Rat
set_option maxHeartbeats 2000000 in
theorem onePlace_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (i : Fin J.r), ∀ n ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v), _root_.GlobalTheory.LevProd.localHomProduct J j hj n i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i → n ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α i n hn hphi
  have hs := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj
  have hj' : j ≤ B.R.m := by omega
  have hjm : j < B.R.m := by omega
  have hI := hW.tr.ok
  have hL := hI.idx_ok (W.P.I.tup t)
  have hrep := hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' hs) hjm (J.ι j α)
  rw [hJ.sec j (by omega) α i] at hrep
  obtain ⟨gl, hglc, hgl, hglu⟩ := GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by omega))
  have hAt : ∀ y, gl y ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v) := fun y =>
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hgl y).1 _ rfl
  have hund : (J.G i).q.v = ((J.P i).1).under (𝓞 B.host.F) := by
    rw [hJ.eq i]; exact (_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).2 i
  have hidem : Formalism.L2.NTheta.IsIdemAt (J.G i).q.e (J.P i).1 := by rw [hJ.eq i]; exact (J.G i).idem
  have hg1 : gramN (I.rec7 l Z) j hj' = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hW.tr.pins.some l Z).2.2.2 j hj').1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj') (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := by rw [hg1]; rfl
  obtain ⟨e, he, heβ⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 j (by have := hs; exact Nat.le_succ_of_le this)
  let K := (GlobalTheory.ClassSumLevel.levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (J.A.K j hj' (J.ι j α)).lev).comap gl
  have hKo : IsOpen (K : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) :=
    (GlobalTheory.ClassSumLevel.isOpen_levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (J.A.K j hj' (J.ι j α)).lev).preimage hglc
  have hle : _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ K := by
    refine prX_le_of_prCat _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by omega) _ _ hrep K hKo (fun e' he' y hy => ?_)
    refine Subgroup.mem_comap.2 ((GlobalTheory.ClassSumLevel.mem_levG_iff _ _ _ _).2 ?_)
    refine mem_lev_of_rat I hI l Z u _ J.A hJ.is j hj (J.ι j α) (hJ.std j (by omega) _) (J.P i) (hJ.tw i).nmem _
      (eU ▸ GlobalTheory.AdForm.Model.finGL_mem _ (rankN (I.rec7 l Z) j hj') _) (fun v' hv' => ?_) y hy (fun r s => ?_)
    · refine GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt _ _ _ _ _ fun w hw r s => ?_
      refine (GlobalTheory.FinMComp.adAt_finM_eq_one (I.rec7 l Z) _ (rankN (I.rec7 l Z) j hj') _ _ (hAt _) w
        (fun h => hv' (hw.symm.trans (h.trans hund))) r s).trans ?_
      rfl
    · obtain ⟨r, rfl⟩ := e'.surjective r
      obtain ⟨s, rfl⟩ := e'.surjective s
      have ee : ∀ c, (finCongr (rankN (I.rec7 l Z) j hj')).symm (e' c) = e c := fun c => Fin.ext ((he' c).trans (he c).symm)
      have h1 := entry_of_std _ e heβ _ _ (hgl (GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e' y)).2 r s
      refine adAt_eq_of_pr (J.G i).q (J.P i).1 hidem
        (mt _ (gl (GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e' y))
          ((finCongr (rankN (I.rec7 l Z) j hj')).symm (e' r)) ((finCongr (rankN (I.rec7 l Z) j hj')).symm (e' s))) _ ?_
      rw [ee, ee]
      exact h1
  have hn' : n = gl (_root_.GlobalTheory.LevProd.localHomProduct J j hj n i) :=
    hglu n _ ((GlobalTheory.LocGl.supp_iff _ _).2 hn) ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
  have hK : gl (_root_.GlobalTheory.LevProd.localHomProduct J j hj n i) ∈ GlobalTheory.ClassSumLevel.levG ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj')
    (J.A.K j hj' (J.ι j α)).lev := hle hphi
  rw [← hn'] at hK
  exact (hJ.is.U j hj' _ n).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hn, hK⟩
theorem mem_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j), ∀ n ∈ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J), (∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj n i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i) → n ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α n hn hphi
  classical
  let Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)) := Finset.univ.image (fun i => (J.G i).q.v)
  have key : ∀ S : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)), S ⊆ Q → ∀ n ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ S),
      (∀ i, (J.G i).q.v ∈ S → _root_.GlobalTheory.LevProd.localHomProduct J j hj n i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i) → n ∈ J.A.U j (J.ι j α) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ n hn _
      rw [grpAt_empty _ (fun w h => by simp at h) n hn]
      exact one_mem _
    | insert v S hvS ih =>
      intro hsub n hn hphi
      obtain ⟨i0, -, hi0⟩ := Finset.mem_image.1 (hsub (Finset.mem_insert_self v S))
      obtain ⟨x, hx, y, hy, rfl⟩ := ((GlobalTheory.FinPl.localComponents _ (fun w => w = v)).2 _).1 n
      have hxS : x ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ insert v S) :=
        grpAt_le_of _ (fun w hw => by rw [hw]; exact Finset.mem_insert_self v S) hx
      have hyS : y ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ S) := by
        have h1 : y ∈ GlobalTheory.FinPl.grpAt _ (fun w => w ∈ insert v S) := by
          have : y = x⁻¹ * (x * y) := by group
          rw [this]; exact mul_mem (inv_mem hxS) hn
        rw [GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts] at h1 ⊢
        rw [GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts] at hy
        refine fun a b => ⟨(h1 a b).1, fun w hw => ?_⟩
        by_cases hwv : w = v
        · exact hy a b w hwv
        · exact (h1 a b).2 w (fun hm => (Finset.mem_insert.1 hm).elim hwv hw)
      have hyv : _root_.GlobalTheory.LevProd.localHomProduct J j hj y i0 = 1 := by
        show GlobalTheory.LevIdx.locHom (J.G i0).q _ _ y = 1
        apply locHom_one_of_off
        rw [hi0]; exact hy
      have hxU : x ∈ J.A.U j (J.ι j α) := by
        refine _root_.GlobalTheory.LevProd.Bwd.onePlace_alt W hW u a ha hTr j hj t J hJ α i0 x (by rw [hi0]; exact hx) ?_
        have := hphi i0 (by rw [hi0]; exact Finset.mem_insert_self v S)
        rwa [map_mul, Pi.mul_apply, hyv, mul_one] at this
      have hyU : y ∈ J.A.U j (J.ι j α) := by
        refine ih (fun w hw => hsub (Finset.mem_insert_of_mem hw)) y hyS (fun i hi => ?_)
        have hxi : _root_.GlobalTheory.LevProd.localHomProduct J j hj x i = 1 := by
          show GlobalTheory.LevIdx.locHom (J.G i).q _ _ x = 1
          apply locHom_one_of_off
          exact GlobalTheory.FinPl.SetCut.grpAt_le_grpOff _ _ _
            (fun p hp hp' => hvS (by rw [← hp, hp']; exact hi)) hx
        have := hphi i (Finset.mem_insert_of_mem hi)
        rwa [map_mul, Pi.mul_apply, hxi, one_mul] at this
      exact mul_mem hxU hyU
  refine key Q subset_rfl n (grpAt_le_of _ (fun w hw => ?_) hn) (fun i _ => hphi i)
  obtain ⟨i, hi⟩ := hw
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
end GlobalTheory.LevProd.Bwd
end
end
