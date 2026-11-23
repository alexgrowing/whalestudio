import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCosetRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmbeddingAtLocalFactor
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiStdEqConstMulLocXi

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLevTyp
section Main
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
set_option maxHeartbeats 2000000 in
theorem cosetIn_p0_eq_of_reads (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 1 = B.R.m) {t t' : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.Reads)
    (α : J.Ch j) {J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'} (hJ' : J'.Reads) (α' : J'.Ch j) (w : (B.primes X).vGs) :
    cosetIn (J.A.p0 j (J.ι j α)) ⟨w.1, Finset.mem_union_left _ w.2⟩ =
      cosetIn (J'.A.p0 j (J'.ι j α')) ⟨w.1, Finset.mem_union_left _ w.2⟩ := by
  obtain ⟨n, hn⟩ := a.pl.surjective ⟨w.1, (hW.lev.2.1 _).2 w.2⟩
  have hP : w.1 = (a.pl n).1 := by rw [hn]
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain rfl : j = (a.G n).s + 1 := by omega
  have hint : ∀ x : B.fields.E, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt w.1 x := by
    have hR := (ha.tie (fun t => (TopLocFac.nonempty_rowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g hTr.pinX.std t).some)
      fun t => (TopLocFac.nonempty_colCh _ _).some).2
    rw [hP]
    exact (GlobalTheory.LocMod.PinEx.place_facts _ (hR.idem n).1).2.1
  have hqv : HeightOneSpectrum.valuation B.fields.E w.1 (Formalism.L2.Col.qOf w.1 : B.fields.E) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨i, g1, -, -, g4, -⟩ := GlobalTheory.SeeSaw.LevelData.type_prime w.2
    exact GlobalTheory.AtTypeExists.valuation_norm w.1 (g1 ▸ g4)
  obtain ⟨e, he⟩ := exists_xOrd B.R ((a.G n).s + 1)
  have key : ∀ {t : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (_ : J.Reads) (α : J.Ch ((a.G n).s + 1)), ∃ z : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1)),
      cosetIn (J.A.p0 _ (J.ι _ α)) ⟨w.1, Finset.mem_union_left _ w.2⟩ =
        {z' | z' - z ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N ((a.G n).s + 1)) w.1} ∧
      ∀ r, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (z (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k] := by
    intro t J hJ α
    refine ⟨_, (coset_at (J.A.p0 _ (J.ι _ α)) hj ((J.A.p0 _ (J.ι _ α)).repY_mem hj) w).1, fun c => ?_⟩
    have hF := _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2 hj (J.ι _ α)
    have hq := TopFrames.intAt_q_mul (A := J.A) ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2 hj (J.ι _ α)
    have hco := hJ.cosG n α e he c
    have hfr : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ α)).1.1 ⟨w.1, Finset.mem_union_left _ w.2⟩ =
      (J.A.p0 _ (J.ι _ α)).1.1.deco.1.liftFr w := dif_pos w.2
    rw [hfr] at hF hq
    generalize (J.A.p0 _ (J.ι _ α)).1.1.deco.1.liftFr w = f at hF hq ⊢
    generalize Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2 = y at hq hco ⊢
    have h1 := (hint _).2 (TopFrames.intAt_sub_of_near hqv hF hq (e c))
    rw [LinearEquiv.apply_symm_apply, map_sub] at h1
    have h2 : _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y (e c)) - (a.G n).S.y0 (Fin B.R.t) c ∈ 𝒪[(a.G n).k] := hco
    have h3 := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at h3
  obtain ⟨z, hz, h1⟩ := key hJ α
  obtain ⟨z', hz', h1'⟩ := key hJ' α'
  have hd : z - z' ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N ((a.G n).s + 1)) w.1 := by
    refine GlobalTheory.TopStep.mem_stdAt.2 fun i => ?_
    obtain ⟨r, rfl⟩ := e.surjective i
    have h := sub_mem (h1 r) (h1' r)
    rw [sub_sub_sub_cancel_right, ← map_sub] at h
    exact (hint _).1 h
  rw [hz, hz']
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have := add_mem h hd
    rwa [sub_add_sub_cancel] at this
  · intro h
    have := sub_mem h hd
    rwa [sub_sub_sub_cancel_right] at this
set_option maxHeartbeats 2000000 in
theorem mem_UAd_iff_of_not_plF (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 1 = B.R.m) [NeZero (B.R.N j)] {t : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t}
    (hJ : J.Reads) (β : J.Ch₀ j) (v : HeightOneSpectrum (𝓞 B.host.F)) (hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal)
    (hv : ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v) (x : TC.GA B (B.R.N j)) (hxU : x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j))
    (hx : ∀ w, w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) w) x = 1) :
    x ∈ (J.A.K j (show j ≤ B.R.m by omega) β).lev.U ↔
      x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
      (GlobalTheory.Mem.Col2.MemChart.chG (X := B.fields) (Formalism.L2.Col.colLevSym I.Ch j) (GlobalTheory.Mem.Col2.MemChart.bar (J.A.p0 j β))) := by
  have hm : j ≤ B.R.m := by omega
  obtain ⟨c, rfl⟩ := (hJ.is.reads j hm).onto β
  have h6 := (TrueColsTest.kStd_spec X u (B.R.N j)).2.1 v hT
  have hk : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (J.A.kb j (J.A.chOf j c)) = 1 := by
    obtain ⟨k₀, h, -, h1, h2, h3, -⟩ := hJ.pen j hj (J.A.chOf j c)
    have h5 := TopFrames.finM_map_prV _ (rankN (I.rec7 l Z) j hm) h3 hv
    refine Units.ext ?_
    have h7 := (hJ.is.kA j hm (J.A.chOf j c)).2.1
    rw [h2, GlobalTheory.AdForm.Model.finM_mul, h1] at h7
    have h8 : (J.A.kb j (J.A.chOf j c)).1.map (Formalism.UG.prV (E := B.host.E) v) = 1 := by
      rw [← h7]
      refine Matrix.map_mul.trans ?_
      have h6' : (TC.kStd X u (B.R.N j)).1.map (Formalism.UG.prV (E := B.host.E) v) = 1 := congrArg Units.val h6
      exact (congrArg₂ (fun x y : Matrix (Fin (B.R.N j)) (Fin (B.R.N j))
        (B.host.E ⊗[B.host.F] v.adicCompletion B.host.F) => x * y) h6' h5).trans (one_mul _)
    exact h8
  have h1 : ∀ P ∈ I.Q (W.P.I.tup t), x.1.map (GlobalTheory.Mem.Col2.adAt B.host.F P) = 1 := fun P hP => by
    refine GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV P (hx _ fun h => hv ?_)
    obtain ⟨i, hi⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
    exact ⟨i, (((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i).trans (congrArg _ hi)).trans h⟩
  refine (mem_lev_iff I hW.tr.ok hW.tr.tw l.pr u _ j hj (hJ.is.reads j hm) c x hxU (commute_of_off hx hk)
    (commute_of_off hx h6) h1).trans ?_
  have hb : GlobalTheory.Mem.Col2.MemChart.bar (show PtAt B.R I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) u j from
      (I.stp u (W.P.I.tup t) j).rep c) = GlobalTheory.Mem.Col2.MemChart.bar (J.A.p0 j (J.A.chOf j c)) := funext fun w =>
    (cos_iff_bar hj w (GlobalTheory.Mem.Col2.MemChart.hqG l.pr w.1 w.2) _ _).1 (congrFun (hJ.is.rep j hm c).2 _)
  exact Iff.of_eq (congrArg (fun C => x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
    (GlobalTheory.Mem.Col2.MemChart.chG (X := B.fields) (Formalism.L2.Col.colLevSym I.Ch j) C)) hb)
end Main
set_option maxHeartbeats 2000000 in
theorem uloc_le_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' v → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' v _ hTv hv hv'
  have hm : j ≤ B.R.m := by omega
  haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
  obtain ⟨hPins⟩ := hW.tr.pins
  have hg1 : gramN (I.rec7 l Z) j hm = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hW.tr.ok hPins l Z).2.2.2 j hm).1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hm) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := by rw [hg1]; rfl
  refine GlobalTheory.stepLevel_uloc_le_of_agree _ _ {w | w ≠ v} (fun x hx hxU => ?_) v (fun h => h rfl)
  have hxA : x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := eU ▸ (((J.A.K j hm (J.ι j α)).lev.U_eq x).1 hxU).1
  have hb : GlobalTheory.Mem.Col2.MemChart.bar (J.A.p0 j (J.ι j α)) = GlobalTheory.Mem.Col2.MemChart.bar (J'.A.p0 j (J'.ι j α')) := funext fun w =>
    (cos_iff_bar hj w (GlobalTheory.Mem.Col2.MemChart.hqG l.pr w.1 w.2) _ _).1 (_root_.GlobalTheory.PenLevTyp.cosetIn_p0_eq_of_reads hW ha hTr j hj hJ α hJ' α' w)
  have h1 := (_root_.GlobalTheory.PenLevTyp.mem_UAd_iff_of_not_plF hW ha hTr j hj hJ (J.ι j α) v hTv hv x hxA hx).1 hxU
  rw [hb] at h1
  exact (_root_.GlobalTheory.PenLevTyp.mem_UAd_iff_of_not_plF hW ha hTr j hj hJ' (J'.ι j α') v hTv hv' x hxA hx).2 h1
end GlobalTheory.PenLevTyp
end
end
