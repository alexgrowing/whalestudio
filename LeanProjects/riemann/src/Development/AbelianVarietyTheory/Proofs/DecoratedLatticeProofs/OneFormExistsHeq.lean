import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

noncomputable section

namespace GlobalTheory.TopVal.OneForm

section Generic

variable {D : D7} {O : Obj D} {c : ℝ}

set_option maxHeartbeats 800000 in

theorem row_of_btw (b : Bundle D O c) (x : R3.TwIn O.ex) (y : Bl.BTw b x) (t : (packB b).P.T)
    (F : Fin (((packB b).P.A3.side3 (packB b).P.Ps (packB b).P.ψs (packB b).P.Zs).nV t) → D.what₂.LL)
    (F' : Fin (((packB b).Q.F.fc (cxW (packB b)).zs).Df1.nV t) → D.what₂.LL) (hF : HEq F F') :
    ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), (packB b).P.I.tup t = x.Y.tup s ∧
      HEq ((packB b).Q.F.eV (cxW (packB b)).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      HEq ((packB b).P.I.jA t ((rV0 D (packB b).P.A3.A (packB b).P.Ps (packB b).P.ψs t).mulVec F)) (x.Y.jA s v) := by
  have key : ∀ k : Bl.RPk b.R b.S, k = Bl.rpkX y.y → ∀ (t : k.P.T)
      (F : Fin ((k.P.A3.side3 k.P.Ps k.P.ψs k.P.Zs).nV t) → D.what₂.LL)
      (F' : Fin ((k.B.Q.F.fc (k.B.Q.Rl.toCx3 k.B.Q.F).zs).Df1.nV t) → D.what₂.LL), HEq F F' →
      ∃ (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL), k.P.I.tup t = x.Y.tup s ∧
        HEq (k.B.Q.F.eV (k.B.Q.Rl.toCx3 k.B.Q.F).zs t F') (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
        HEq (k.P.I.jA t ((rV0 D k.P.A3.A k.P.Ps k.P.ψs t).mulVec F)) (x.Y.jA s v) := by
    intro k hk
    subst hk
    intro t F F' hF
    have e : F = F' := eq_of_heq hF
    subst e
    refine ⟨t, (rV0 D x.A3.A x.F.P1 x.F.ψ1 t).mulVec F, rfl, heq_of_eq ?_, HEq.rfl⟩
    have hOk := y.intersectionNumber_baseChange.ok
    have hb : BlockHyp (x.A3.A.fam.R t) (x.A3.A.fam.lvl x.F.P1 x.F.ψ1) x.A3.A.fam.v0 1 :=
      ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
    have key := BlockDat.lf_lvl_vE hb
    unfold R3.rowForm rV0
    show (x.A3.A.fam.R t).S.basis.equivFun.symm (((x.A3.A.fam.R t).vE (x.A3.A.fam.lvl x.F.P1 x.F.ψ1)) *ᵥ F) = _
    congr 1
    conv_lhs => rw [← key]
    rw [Matrix.mul_assoc]
    exact (Matrix.mulVec_mulVec _ _ _).symm
  exact key (Bl.rpkB b) y.eq t F F' hF

end Generic

section Rows

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl

set_option maxHeartbeats 800000 in

theorem row_of_pack {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (x : R3.TwIn ex)
    {G : Type} [g : Group G] [fi : Fintype G] {Pl0 I0 T0 : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m)
    {C : Formalism.L2.Pj.CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) = ⟨G, g, fi, Pl0, I0, T0, A3, C, al, R, F, cG⟩)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (hP : F.P1 = P) (hψ : HEq F.ψ1 ψ)
    (τ : T0 → D.what₂.Tup) (j : ∀ s, (Fin (rDim D A3.A P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (τ s))
    (hτ : HEq x.Y.tup τ) (hj : HEq x.Y.jA j) (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL) :
    ∃ (s' : T0) (v' : Fin (rDim D A3.A P ψ s') → D.what₂.LL), x.Y.tup s = τ s' ∧
      HEq (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) (R3.rowForm A3.A P ψ s' v') ∧ HEq (x.Y.jA s v) (j s' v') := by
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  subst hP
  cases hψ
  cases hτ
  cases hj
  exact ⟨s, v, rfl, HEq.rfl, HEq.rfl⟩

set_option maxHeartbeats 800000 in

theorem row_of_args {K : Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : R3.TwArgs ex t) (s : a.x.T)
    (v : Fin (rDim (w.st Z).toD7 a.x.A3.A a.x.F.P1 a.x.F.ψ1 s) → (w.st Z).toD7.what₂.LL) :
    ∃ (s' : R3.TupU w.I (R3.usedOf w.I T Wt))
      (v' : Fin (rDim (w.st Z).toD7 (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s') → (w.st Z).toD7.what₂.LL),
      a.x.Y.tup s = t.r.Y.tup s' ∧
      HEq (R3.rowForm a.x.A3.A a.x.F.P1 a.x.F.ψ1 s v) (R3.rowForm (D := (w.st Z).toD7) (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s' v') ∧
      HEq (a.x.Y.jA s v) (t.r.Y.jA s' v') :=
  row_of_pack a.x (R3.famT t) a.pack (R3.lev1 w.I) (R3.chr1 w.I) rfl HEq.rfl t.r.Y.tup t.r.Y.jA a.tup a.jA s v

set_option maxHeartbeats 800000 in

theorem rowForm_all (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (R3.Gc X.B px → X.B.LL)) (tr : R3.TrI X.B px) (s : R3.TupU I U) (a : I.ι) (h : s.1 = I.tup a)
    (v : Fin (rDim X.toD7 (R3.famR X I hX U Xg tr).A (R3.lev1 I) (R3.chr1 I) s) → X.toD7.what₂.LL) :
    ∃ v' : Fin (rDim X.toD7 (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a)) → X.toD7.what₂.LL,
      (∀ i i', Fin.val i = Fin.val i' → v' i = v i') ∧
      HEq (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) v')
        (R3.rowForm (D := X.toD7) (R3.famR X I hX U Xg tr).A (R3.lev1 I) (R3.chr1 I) s v) := by
  obtain ⟨τ, hτ⟩ := s
  dsimp only at h
  subst h
  exact ⟨v, fun i i' e => congrArg v (Fin.ext e), HEq.rfl⟩

set_option maxHeartbeats 800000 in

theorem one_form_rows {K : Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} (rx : RXs t) (s : R3.TupU w.I (R3.usedOf w.I T Wt))
    (v : Fin (rDim (w.st Z).toD7 (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s) → (w.st Z).toD7.what₂.LL) :
    ∃ φ : Frm w.I (t.r.Y.tup s),
      IsRes φ (R3.rowForm (D := (w.st Z).toD7) (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s v) ∧
      ∀ u, RecVal (I := w.I) (l := w.l) (Z := Z) u (t.r.Y.tup s) φ (t.r.Y.jA s v) := by
  have hs : s.1 = w.I.tup (t.r.Y.tup s) :=
    (R3.tup_ixOf w.I s).symm.trans (congrArg w.I.tup (t.r.tup_ix s)).symm
  obtain ⟨v', hv, hf⟩ := rowForm_all (w.st Z) w.I t.hX _ t.r.z.Xg t.r.z.tr s (t.r.Y.tup s) hs v
  have hj : rx.all.jA (t.r.Y.tup s) v' = t.r.Y.jA s v := (rx.jA_use s).2 v' v hv
  obtain ⟨x, ⟨φ, hφ, hres, hx⟩, he⟩ := rx.crd (t.r.Y.tup s) v'
  subst hx
  refine ⟨φ, ⟨_, hres.trans hf⟩, fun u => ?_⟩
  rw [← hj, he]
  have key : ∀ (a : w.C.Tup) (φ : Frm w.I a) hφ,
      RecVal (I := w.I) (l := w.l) (Z := Z) u a φ (rx.e a (Df.toCx w.I t.hX a ⟨φ.1, hφ⟩)) := by
    intro a φ hφ
    refine ⟨fun h => ?_, fun p => rx.eMtTw u a _ p⟩
    subst h
    exact fun p => rx.eMt0 u _ p
  exact key _ φ hφ

end Rows

theorem one_form_congr {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : Col2.TC B X} {l : I.Laws} {Z : Col2.TC.Later B (I.cols l)}
    {a a' : (I.rec7 l Z).what₂.Tup} {V V' : Type} {x : V} {x' : V'} {G : (I.rec7 l Z).what₂.Amb a} {G' : (I.rec7 l Z).what₂.Amb a'}
    (ha : a = a') (hx : HEq x x') (hG : HEq G G') (h : ∃ φ : Frm I a', IsRes φ x' ∧ ∀ u, RecVal u a' φ G') :
    ∃ φ : Frm I a, IsRes φ x ∧ ∀ u, RecVal u a φ G := by
  subst ha
  cases hx
  cases hG
  exact h

set_option maxHeartbeats 800000 in

theorem one_form {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) (rx : Bl.RXs q.x.what₂) (s : x.T)
    (v : Fin (rDim (q.w.D q.Z) x.A3.A x.F.P1 x.F.ψ1 s) → (q.w.D q.Z).what₂.LL) :
    ∃ φ : Frm q.w.I (x.Y.tup s), IsRes φ (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) ∧
      ∀ u, RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u (x.Y.tup s) φ (x.Y.jA s v) := by
  have e : a.x = x := eq_of_heq ax
  subst e
  obtain ⟨s', v', k1, k2, k3⟩ := row_of_args (w := q.w) (Z := q.Z) (ex := q.O.ex) (t := q.x.what₂) a s v
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) k1 k2 k3 (one_form_rows rx s' v')

set_option maxHeartbeats 800000 in

theorem recVal_packB : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → Nonempty (Bl.RXs q.x.what₂) → ∀ (t : (packB b).P.T) (F : Fin (((packB b).P.A3.side3 (packB b).P.Ps (packB b).P.ψs (packB b).P.Zs).nV t) → (q.w.D q.Z).what₂.LL) (F' : Fin (((packB b).Q.F.fc (cxW (packB b)).zs).Df1.nV t) → (q.w.D q.Z).what₂.LL), HEq F F' → ∃ φ : GlobalTheory.TopVal.Frm q.w.I ((packB b).P.I.tup t), GlobalTheory.TopVal.IsRes φ ((packB b).Q.F.eV (cxW (packB b)).zs t F') ∧ ∀ u, GlobalTheory.TopVal.RecVal (I := q.w.I) (l := q.w.l) (Z := q.Z) u ((packB b).P.I.tup t) φ ((packB b).P.I.jA t ((rV0 (q.w.D q.Z) (packB b).P.A3.A (packB b).P.Ps (packB b).P.ψs t).mulVec F)) := by
  intro hL p K q c b hb hR t F F' hF
  obtain ⟨rx⟩ := hR
  obtain ⟨s, v, h1, h2, h3⟩ := row_of_btw b hb.x hb.y t F F' hF
  exact one_form_congr (I := q.w.I) (l := q.w.l) (Z := q.Z) h1 h2 h3 (one_form q hb.x hb.a hb.ax rx s v)

end GlobalTheory.TopVal.OneForm

end
