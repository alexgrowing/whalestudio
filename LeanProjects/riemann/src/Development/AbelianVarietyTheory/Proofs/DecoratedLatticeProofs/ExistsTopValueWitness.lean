import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Col GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top GlobalTheory.TopVal

namespace GlobalTheory.TopVal

def DatVal {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {G : Type} [Group G] [Fintype G]
    {Pl0 T : Type} {A : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [aK : Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) A Ks) (tup : T → I.ι) : Prop :=
  ∃ c : Val B →ₛₗ[B.embLL] R.cX.W,
    (∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
      GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = R.cX.ρ γ.1 (c v)) ∧
    ∀ (t : T) (φ : Frm I (tup t)) (x : A.fam.amb.FR t), IsRes φ x →
      ∀ (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') y, HasMat h y → IsUni B y →
        (R.HX t).e (R.jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h) = c (val φ (latOf I (tup t) y))

theorem matEq_of_hasMat {D : D7} {h : GA D D.sp.X'} {y} (hm : HasMat h y) :
    GlobalTheory.Mem.R3.MatEq (R3.matIn D.sp.X' 1 ((finHom D.sp.X').rangeRestrict h)) y := by
  refine ⟨Formalism.L2.Forms.rankP D, fun i j i' j' hi hj => ?_⟩
  have e1 : finCongr (Formalism.L2.Forms.rankP D) i = i' := Fin.ext hi
  have e2 : finCongr (Formalism.L2.Forms.rankP D) j = j' := Fin.ext hj
  rw [← e1, ← e2, ← hm.2 i j]
  unfold R3.matIn
  rw [mul_one]
  rfl

set_option maxHeartbeats 1000000 in

theorem datVal_rows (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : Bl.RowsT K w Z Wt p0) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := t.r.z.alg) t.r.z.R.toRealDat t.r.Y.tup := by
  obtain ⟨c, h1, h2, -, -⟩ := hs.1
  have h3 := t.r.z.pins.char.base.models.jX
  have h4 := t.r.z.lev.beta.2
  refine ⟨c, fun γ γE g hr hm v => h1 γ γE g hr hm v, fun s => ?_⟩
  have h5 : w.I.tup (t.r.Y.tup s) = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have key : ∀ (a : w.I.ι), w.I.tup a = s.1 → ∀ (φ : Frm w.I a) (x : (R3.famT t).A.fam.amb.FR s), IsRes φ x →
      ∀ (h : GA (w.D Z) (w.D Z).sp.X') y, HasMat h y → IsUni B y →
        t.r.z.R.B.jR s x ((finHom (w.D Z).sp.X').rangeRestrict h) = c (val φ (latOf w.I a y)) := by
    intro a ha
    obtain ⟨s, hs'⟩ := s
    change w.I.tup a = s at ha
    subst ha
    rintro φ x ⟨ok, hx⟩ h y hm hu
    have hx' : ((by with_unfolding_all exact ((mtildeKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a)).res ok φ :)) : (R3.famT t).A.fam.amb.FR ⟨w.I.tup a, hs'⟩) = x := by
      apply eq_of_heq
      exact (by with_unfolding_all exact (hx :))
    have hM := matEq_of_hasMat hm
    have e := h2 B.sp.cm ⟨w.I.tup a, hs'⟩ ⟨⟨ok⟩, φ⟩ ((finHom (w.D Z).sp.X').rangeRestrict h) ⟨y, hu⟩ (by rw [h4]; exact hM)
    have e2 := decoPt_mk B.sp.cm (B.R.N B.R.m - 1) ∅ (rowSG (B.primes w.px) w.I.sel (w.I.tup a)) ⟨y, hu⟩
    rw [← hx']
    refine Eq.trans ((by with_unfolding_all exact (e :))) (congrArg (fun d => c (val φ d)) e2)
  intro φ x hx h y hm hu
  exact (congrFun (h3 s x) _).trans (key _ h5 φ x hx h y hm hu)

set_option maxHeartbeats 1000000 in

theorem datVal_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := a.x.alg) a.x.R.toRealDat a.x.Y.tup := by
  have h := datVal_rows K B f T w Z Wt ex.p0 t hs
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  rw [← hT'] at h
  obtain ⟨c, h1, h2⟩ := h
  refine ⟨(by with_unfolding_all exact (c :)), ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h2 :))

set_option maxHeartbeats 1000000 in

theorem pkVal_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → q.x.what₂.r.z.Std → ∃ cv, GlobalTheory.TopVal.ValEqv (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b) cv ∧ GlobalTheory.TopVal.PkVal (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b) cv := by
  intro hL p K q c b hw hs
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := datVal_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a hs
  have h1 : DatVal q.w.I q.w.l q.Z (aK := x.alg) x.R.toRealDat x.Y.tup := by
    subst hx
    exact h0
  have h2 : (fun k : Bl.RPk b.R b.S => DatVal q.w.I q.w.l q.Z (aK := k.B.alg) k.B.Q.Rl.toRealDat k.P.I.tup) (Bl.rpkB b) := by
    rw [y.eq]
    exact h1
  obtain ⟨cv, h3, h4⟩ := h2
  exact ⟨cv, h3, h4⟩

end GlobalTheory.TopVal
