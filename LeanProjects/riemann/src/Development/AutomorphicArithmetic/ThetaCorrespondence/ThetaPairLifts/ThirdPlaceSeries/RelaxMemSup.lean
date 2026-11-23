import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlMemLevelStatement
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
namespace GlobalTheory.LevProd.Supp
section Cut
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut
set_option synthInstance.maxHeartbeats 200000
variable {D : D7}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Cut
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}
end Level
section Std
open Formalism.L2.Col Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)
end Std
section Main
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
set_option maxHeartbeats 2000000 in
theorem mem_U_iff_mem_levU_of_grpAt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) [NeZero (B.R.N j)] {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
    (hJ : J.Reads) (β : J.Ch₀ j) {P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop} (hP : ∀ v, P v → ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J v)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hg : g ∈ GlobalTheory.FinPl.grpAt _ P) (x : TC.GA B (B.R.N j))
    (hxU : x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j)) (hx : x.1 = finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) g) :
    g ∈ J.A.U j β ↔ x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
      (Formalism.L2.Col.colLevSym I.Ch j).grp := by
  have hj' : j ≤ B.R.m := by omega
  rw [← mem_lev_iff I hW.tr.ok hW.tr.tw l.pr u _ j (by omega) (hJ.is.reads j hj') β (hJ.std j (by omega) β) x hxU fun Q hQ r s => ?_]
  · rw [hJ.is.U j hj']
    refine ⟨fun ⟨_, κ, hκ⟩ => ?_, fun h => ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hg, ⟨x, h⟩, hx⟩⟩
    have e : x = κ.1 := Units.ext (hx.trans hκ.symm)
    rw [e]
    exact κ.2
  · rw [hx]
    refine GlobalTheory.FinMComp.adAt_finM_eq_one _ _ _ P g hg Q (fun h => hP _ h ?_) r s
    obtain ⟨i, hi⟩ := hJ.surj Q ((hW.tq.Q t Q).2 hQ)
    exact ⟨i, ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i).trans (congrArg _ hi)⟩
set_option maxHeartbeats 2000000 in
theorem mem_U_of_mem_U_away_from_twisted (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t' : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
    (hJ : J.Reads) (β : J.Ch₀ j) (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t') (hJ' : J'.Reads) (β' : J'.Ch₀ j) {P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop}
    (hP : ∀ v, P v → ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J v) (hP' : ∀ v, P v → ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J' v)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hg : g ∈ GlobalTheory.FinPl.grpAt _ P) (h : g ∈ J.A.U j β) : g ∈ J'.A.U j β' := by
  have hj' : j ≤ B.R.m := by omega
  haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
  obtain ⟨hPins⟩ := hW.tr.pins
  have hg1 : gramN (I.rec7 l Z) j hj' = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hW.tr.ok hPins l Z).2.2.2 j hj').1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj') (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := by rw [hg1]; rfl
  obtain ⟨x, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (gramN (I.rec7 l Z) j hj') rfl g
  have hxU : x.1 ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := eU ▸ x.2
  exact (_root_.GlobalTheory.LevProd.Supp.mem_U_iff_mem_levU_of_grpAt hW ha hTr j hj J' hJ' β' hP' hg x.1 hxU hx).2 ((_root_.GlobalTheory.LevProd.Supp.mem_U_iff_mem_levU_of_grpAt hW ha hTr j hj J hJ β hP hg x.1 hxU hx).1 h)
set_option maxHeartbeats 2000000 in
theorem cutAt_mem_U_of_mem_relax_not_twAt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t' : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
    (hJ : J.Reads) (α : J.Ch j) (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t') (hJ' : J'.Reads) (α' : J'.Ch j)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hg : g ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α) (v : GlobalTheory.FinPl.Pl (I.rec7 l Z)) (hv' : ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J' v) :
    cutAt _ v g ∈ J'.A.U j (J'.ι j α') := by
  obtain ⟨⟨hsup, hgf⟩, hphi⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
  by_cases hv : _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J v
  · obtain ⟨i, rfl⟩ := hv
    obtain ⟨gl, -, h1, h2⟩ := GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
      (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)))
    have hy : _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := (Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i (Set.mem_univ _)
    rw [h2 (cutAt _ (J.G i).q.v g) (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i) (suppAt_cutAt _ _ g)
      ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 (locHom_cutAt _ _ _ hgf).symm)]
    exact _root_.GlobalTheory.T.true_geometry_lattice_open_alt W hW u a ha hTr j hj t' J' hJ' α' t J hJ i hv' gl h1 _ hy
  · have hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J) ≤ (J.A.U j (J.ι j α)).comap (cutAt _ v) := by
      refine sup_le (fun x hx => ((mem_U_iff hJ.is j (by omega) _ x).1 hx).2 v) fun x hx => ?_
      rw [Subgroup.mem_comap, cutAt_eq_one _ hv hx]
      exact one_mem _
    exact _root_.GlobalTheory.LevProd.Supp.mem_U_of_mem_U_away_from_twisted hW ha hTr j hj J hJ _ J' hJ' _ (P := (· ∈ ({v} : Finset _)))
      (fun w hw h => hv (Finset.mem_singleton.1 hw ▸ h)) (fun w hw h => hv' (Finset.mem_singleton.1 hw ▸ h)) (cutAt_mem _ v g) (hle hsup)
end Main
set_option maxHeartbeats 2000000 in
theorem relax_mem_sup_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j), ∀ g ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α, g ∈ J'.A.U j (J'.ι j α') ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' g hg
  have hgf : g ∈ GfC _ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2
  let Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J'.G i).q.v
  have hQ : ∀ v, v ∈ Q ↔ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J' v := fun v => by
    simp only [Q, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  have h1 := GlobalTheory.FinPl.SetCut.cutG_mem_Q _ Q g
  have h2 := GlobalTheory.FinPl.SetCut.cutG_mem_Qc _ Q hgf
  have e := GlobalTheory.FinPl.SetCut.cutG_mul_cutG _ Q g
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.idemQ_mul_self Q) g = g₁ at h1 e
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) g = g₂ at h2 e
  have h3 : g₂ ∈ J'.A.U j (J'.ι j α') := by
    refine (mem_U_iff hJ'.is j (by omega) _ g₂).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h2, fun v => ?_⟩
    by_cases hv : v ∈ Q
    · rw [cutAt_eq_one _ (P := (· ∉ Q)) (not_not.2 hv) h2]
      exact one_mem _
    · have h4 := _root_.GlobalTheory.LevProd.Supp.cutAt_mem_U_of_mem_relax_not_twAt hW ha hTr j hj J hJ α J' hJ' α' hg v fun h => hv ((hQ v).2 h)
      rwa [← e, map_mul, cutAt_eq_one _ (P := (· ∈ Q)) hv h1, one_mul] at h4
  rw [← e]
  exact mul_mem (Subgroup.mem_sup_right (grpAt_mono _ (fun v hv => (hQ v).1 hv) h1)) (Subgroup.mem_sup_left h3)
end GlobalTheory.LevProd.Supp
end
end
