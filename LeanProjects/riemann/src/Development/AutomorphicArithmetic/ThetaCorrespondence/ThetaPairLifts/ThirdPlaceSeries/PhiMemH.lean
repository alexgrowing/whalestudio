import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeMeasureValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.LevProd.Fwd
section Columns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Col2.PtExist
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
end Columns
section Local
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
end Local
section Split
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.AdForm GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Split
end GlobalTheory.LevProd.Fwd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
namespace GlobalTheory.LevProd.Fwd
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
set_option maxHeartbeats 1000000 in
theorem mem_prCat_of_pr_eq (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads) (j : ℕ) (hj : j + 2 ≤ B.R.m) (β : J.Ch₀ j)
    (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (hg : g ∈ J.A.U j β)
    (y : Fin J.r → (Formalism.L2.Col.Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Formalism.L2.Col.Sp B.fields.E (B.R.N j)))
    (hy : ∀ i r s, (J.G i).q.pr (mt _ g (Fin.cast (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)).symm r)
      (Fin.cast (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)).symm s)) = (J.G i).q.pr (incA (I.rec7 l Z) (y i (Pi.single s 1) r))) (i : Fin J.r) :
    y i ∈ Formalism.L2.Col.prCat (Pr := B.primes X) (I.cst (W.P.I.tup t)).sharp j (J.P i).1
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get (show j < B.R.m by omega)) (J.P i)) := by
  have hjm : j ≤ B.R.m := by omega
  have hA := hJ.is
  have hI := hW.tr.ok
  have hL := hI.idx_ok (W.P.I.tup t)
  obtain ⟨hP⟩ := hW.tr.pins
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hjm β
  obtain ⟨-, κ, hκ⟩ := (hA.U j hjm _ g).1 hg
  have hd : Disjoint (B.primes X).vGs (I.Q (W.P.I.tup t)) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I _) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have huni : κ.1 ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) := by
    have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hjm).1
    have huni : ∀ (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hjm) (B.T u)
        (I.rec7 l Z).R.f (J.A.bad j)) (x : TC.GA B (B.R.N j)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) := by
      intro S x hx
      have h := ((S.U_eq x).1 hx).1
      rw [hgram] at h
      exact h
    exact huni _ κ.1 κ.2
  have hloc : ∀ PP i, J.pl i = PP →
      GlobalTheory.Mem.ColAd.locM (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) PP κ.1 = GlobalTheory.Mem.ColAd.ratM PP (y i) := by
    rintro _ i rfl
    exact locM_of_pr (J.G i).q (J.pl i) (J.G i).idem _ _ g κ.1 hκ (y i) (hy i)
  have hsurj : ∀ P : I.Q (W.P.I.tup t), ∃ i, J.pl i = P.1 := fun P => hJ.surj P.1 ((hW.tq.Q t P.1).2 P.2)
  choose ι hι using hsurj
  have hmem : J.pl i ∈ I.Q (W.P.I.tup t) := (hW.tq.Q t _).1 (J.mem i)
  obtain ⟨κ', hκ', e'⟩ := mem_levQ I hI (hA.reads j hjm) c κ.1 huni κ.2 (fun P => by
      rw [hJ.std j (by omega)]
      refine Matrix.ext fun r s => ?_
      refine (GlobalTheory.Fam.MovedJoin.adAt_kStd_of_twist hI _ ⟨P.1, Finset.mem_union_right _ P.2⟩
        (Finset.disjoint_right.1 hd P.2) u _ r s).trans ?_
      rw [Matrix.one_apply]
      split_ifs <;> simp)
    (fun P => y (ι P)) (fun P => hloc _ _ (hι P)) ⟨J.pl i, hmem⟩
  have hii : ι ⟨J.pl i, hmem⟩ = i := hJ.inj (hι ⟨J.pl i, hmem⟩)
  rw [hii] at e'
  have hb : levQAt I.sel (I.tup (W.P.I.tup t)) (I.idx (W.P.I.tup t)) (I.Tp (W.P.I.tup t)) j c.1 =
      (I.idx (W.P.I.tup t)).levQ j ((J.A.b0 j (J.A.chOf j c)).get (show j < B.R.m by omega)) := by
    rw [← (hA.rep j hjm c).1]
    unfold levQAt Idx.get
    conv_lhs => rw [← Option.some_get (c.1.2.2 (show j < B.R.m by omega))]
    rfl
  rw [hb, hL.grpQ, Subgroup.mem_subgroupOf, e'] at hκ'
  have hPi : J.P i = ⟨J.pl i, Finset.mem_union_right _ hmem⟩ := Subtype.ext (hJ.eq i)
  rw [hPi]
  exact hκ'
end GlobalTheory.LevProd.Fwd
namespace GlobalTheory.LevProd
open GlobalTheory.LevProd.Fwd
set_option maxHeartbeats 1000000 in
theorem phi_mem_H_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j), ∀ g ∈ J.A.U j (J.ι j α), ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α g hg
  have hjm : j ≤ B.R.m := by omega
  have hL := hW.tr.ok.idx_ok (W.P.I.tup t)
  obtain ⟨hP⟩ := hW.tr.pins
  have hrk := rankN (I.rec7 l Z) j hjm
  have hstd := fun i : Fin J.r => (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; exact this.trans (Nat.le_succ _))
  choose e he hF using hstd
  let e₀ : Fin J.r → (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ≃ Fin ((I.rec7 l Z).R.N j)) := fun i => (e i).trans (finCongr hrk)
  have key := fun i : Fin J.r => prCat_iff _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega) _ _
      (hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)) (by omega) (J.ι j α)) (e₀ i) (fun r => he i r)
  have hHo : ∀ i, IsOpen (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) := fun i => by
    have h := (key i).1
    rw [hJ.sec j hjm α i] at h
    exact h
  have hHr : ∀ i y, y ∈ Formalism.L2.Col.prCat (Pr := B.primes X) (I.cst (W.P.I.tup t)).sharp j (J.P i).1
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j (J.ι j α)).get (show j < B.R.m by omega)) (J.P i)) →
      GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) y ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := fun i y hy => by
    have h := ((key i).2 y).1 hy
    rw [hJ.sec j hjm α i] at h
    exact h
  have hUo := (GlobalTheory.ChartReps.twDat_reps I hW.tr.ok hP l Z u _ _ J.A hJ.is j hjm (J.ι j α)).1.opn
  have hgl := fun i : Fin J.r => GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega))
  choose gl hglc hglp _ using hgl
  have hAt : ∀ i x, gl i x ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v) := fun i x =>
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hglp i x).1 _ rfl
  have hVo : ∀ i, IsOpen {x | gl i x ∈ J.A.U j (J.ι j α)} := fun i =>
    hUo.preimage (f := fun x => (⟨gl i x, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hAt i x)⟩ : GfC _)) ((hglc i).subtype_mk _)
  have hy : ∀ i, ∃ y, GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) y ∈
      (fun v => (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i)⁻¹ * v) ⁻¹' ((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set _) ∩ {x | gl i x ∈ J.A.U j (J.ι j α)}) := fun i =>
    GlobalTheory.denseGL_completion _ (J.G i).compl.dense (e₀ i) (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i) _
      (((hHo i).inter (hVo i)).preimage (continuous_const.mul continuous_id))
      (by
        rw [Set.mem_preimage, inv_mul_cancel]
        exact ⟨one_mem _, by rw [Set.mem_setOf_eq, map_one]; exact one_mem _⟩)
  choose y hy using hy
  set x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k := fun i =>
    (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i)⁻¹ * GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) (y i) with hx
  have hphi : ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj (gl i (x i)) = Pi.mulSingle i (x i) := by
    intro i
    funext i'
    show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl i (x i)) = _
    by_cases h : i' = i
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 ((hglp i' (x i')).2)).symm
    · rw [Pi.mulSingle_eq_of_ne h]
      exact locHom_eq_one (J.G i).q (J.G i').q _ _
        (fun hv => h ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).1 hv)) (hAt i _)
  have hg' : g * ((List.finRange J.r).map fun i => gl i (x i)).prod ∈ J.A.U j (J.ι j α) := by
    refine mul_mem hg (Subgroup.list_prod_mem _ fun z hz => ?_)
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
    exact (hy i).2
  have hφ' : ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj (g * ((List.finRange J.r).map fun i => gl i (x i)).prod) i =
      GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) (y i) := by
    intro i
    rw [map_mul, map_list_prod, List.map_map]
    simp only [Function.comp_def, hphi]
    rw [list_prod_mulSingle x, Pi.mul_apply]
    exact mul_inv_cancel_left _ _
  intro i
  have h1 := hHr i _ (_root_.GlobalTheory.LevProd.Fwd.mem_prCat_of_pr_eq hW J hJ j hj _ _ hg' y (fun i r s => by
    obtain ⟨r, rfl⟩ := (e₀ i).surjective r
    obtain ⟨s, rfl⟩ := (e₀ i).surjective s
    exact (locHom_std (J.G i).q _ _ (e i) (hF i) _ r s).symm.trans (congrArg (fun z => z.val r s) (hφ' i))) i)
  have h2 : x i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := (hy i).1
  have h3 := mul_mem h1 (inv_mem h2)
  rw [hx] at h3
  simpa using h3
end GlobalTheory.LevProd
end
end
