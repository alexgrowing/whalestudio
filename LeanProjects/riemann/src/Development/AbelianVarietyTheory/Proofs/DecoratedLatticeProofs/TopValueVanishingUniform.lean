import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSwapR
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCopy
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal.Inj

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem exists_fin {D : D7} (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) :
    ∃ g' : GA D V, g' ∈ GfC V ∧ finHom V g' = finHom V g ∧
      ∃ y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        y ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
        ∀ i j, (Formalism.UG.bc (swapAE D) (finHom V g')).1 i j = y.1 (finCongr hn i) (finCongr hn j) := by
  subst hn
  let z := (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).symm (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g)
  have hz : GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram z.1 = GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g :=
    (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).apply_symm_apply _
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V _ rfl
  refine ⟨z.1, z.2, congrArg Subtype.val hz, (e ⟨z.1, z.2⟩).1, (e ⟨z.1, z.2⟩).2, fun i j => ?_⟩
  rw [he]
  rfl

theorem eq_zero_of_models {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g, (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  have h1 : R.B.jR t x = 0 := by
    funext k
    obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective k
    exact (congrFun (h t x) k).symm.trans ((congrArg ((R.HX t).e (R.jX t x)) hg.symm).trans (hx g))
  have h2 : Function.Injective (R.B.jR t) := GlobalTheory.PresBasic.extL_injective (R.B.R t).pres
  exact (injective_iff_map_eq_zero (R.B.jR t)).1 h2 x h1

theorem eq_zero_of_isRes {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : Col2.TC B X) (a : I.ι) (φ : Frm I a) τ (e : I.tup a = τ)
    (ok : (Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).Ok)
    (h : IsRes φ (0 : ((Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).toCSD ok).Forms)) : φ = 0 := by
  subst e
  obtain ⟨ok', h⟩ := h
  exact (LinearEquiv.map_eq_zero_iff _).1 (eq_of_heq h)

set_option maxHeartbeats 2000000 in

theorem eq_zero_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) :
    ∀ (s : a.x.T) (φ : Frm w.I (a.x.Y.tup s)), IsRes φ (0 : a.x.A3.A.fam.amb.FR s) → φ = 0 := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  intro s φ h
  have e : w.I.tup (Y.tup s) = s.1 :=
    (congrArg w.I.tup ((congrFun hT' s).trans (t.r.tup_ix s))).trans (R3.tup_ixOf w.I s)
  exact eq_zero_of_isRes w.I _ φ s.1 e _ h

theorem exists_hasMat {D : D7} (gP : Formalism.L2.Forms.gramP D = 1) (g : GA D D.sp.X') :
    ∃ g' y, GlobalTheory.Core.Rk.Top.HasMat g' y ∧ y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) ∧
      (finHom D.sp.X').rangeRestrict g = (finHom D.sp.X').rangeRestrict g' := by
  obtain ⟨g', h1, h2, y, h3, h4⟩ := exists_fin _ _ (Formalism.L2.Forms.rankP D) g
  have h6 : y ∈ Formalism.UG.UPts _ (Formalism.L2.Forms.gramP D) _ := h3
  rw [gP] at h6
  exact ⟨g', y, ⟨h1, h4⟩, h6, Subtype.ext h2.symm⟩

theorem eq_zero_of_hasMat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (gP : Formalism.L2.Forms.gramP D = 1)
    (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) →
      (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  refine eq_zero_of_models R h t x fun g => ?_
  exact (exists_hasMat gP g).elim fun g' h1 => h1.elim fun y h2 =>
    (congrArg ((R.HX t).e (R.jX t x)) h2.2.2).trans (hx g' y h2.1 h2.2.1)

theorem eq_zero_of_pkAt {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : Col2.TC B X} {l : I.Laws} {Z : Col2.TC.Later B (I.cols l)}
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)
    (gP : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t)
    (hz : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → IsUni B y → pkAt W t x g = 0) : x = 0 := by
  exact eq_zero_of_hasMat (pk W) W.Q.charW.base.models.jX gP t x hz

set_option maxHeartbeats 1000000 in

theorem val_eq_zero : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ (t : (packB b).P.T) (φ : GlobalTheory.TopVal.Frm q.w.I ((packB b).P.I.tup t)) (x : (packB b).P.A3.A.fam.amb.FR t), GlobalTheory.TopVal.IsRes φ x → (∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → GlobalTheory.TopVal.IsUni q.B y → GlobalTheory.TopVal.pkAt (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b) t x g = 0) → ∀ d, GlobalTheory.TopVal.val φ d = 0 := by
  intro hL p K q c b hw t φ x hx hz d
  have hx0 : x = 0 := eq_zero_of_pkAt (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b)
    (Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z).2.1 t x hz
  subst hx0
  obtain ⟨x, a, ax, y, -⟩ := hw
  have e : a.x = x := eq_of_heq ax
  subst e
  have h0 := eq_zero_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have key : ∀ k : Bl.RPk b.R b.S, k = Bl.rpkX y.y →
      ∀ (s : k.P.T) (φ : Frm q.w.I (k.P.I.tup s)), IsRes φ (0 : k.P.A3.A.fam.amb.FR s) → φ = 0 := by
    intro k hk
    subst hk
    exact h0
  rw [key (Bl.rpkB b) y.eq t φ hx]
  rfl

end GlobalTheory.TopVal.Inj
