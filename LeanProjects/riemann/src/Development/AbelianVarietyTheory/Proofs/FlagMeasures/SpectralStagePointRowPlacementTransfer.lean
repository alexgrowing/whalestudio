import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.See
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToSTiesRPin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JoinSIOnV0
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.StageMove

def StageAt {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ) : Prop :=
  SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧
    RowJ R eE P.X P.inst P.G t S.j

set_option maxHeartbeats 1000000 in

theorem stageAt_upd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (k : ℝ) (lam : type_of% R.lam3) (e : type_of% (R.updS k lam).err0) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (h : StageAt R.toRealDat F.lv2 eE P S t c) :
    StageAt ((R.updS k lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 eE P S t c :=
  ⟨⟨h.1.fin, h.1.conj, h.1.mat⟩, h.2.1, h.2.2⟩

set_option maxHeartbeats 1000000 in

theorem spectralStage_point_rowPlacement_transfer : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) (F0 : ∀ u, Formalism.L2.Forms.Forms0 (w.st Z).toD7 u) (s : SAt (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y.eE F0), SeeAt a.x.R.toRealDat a.x.F.lv2 s.P.X s.P.inst s.t ∧ EvalTieT (MP a.x.R.toRealDat) a.x.R.toRealDat.ν0 a.x.R.toRealDat.fd0 (EP a.x.R.toRealDat a.x.F.lv2) s.P.X s.P.G (iotaX s.P.X s.P.inst).toMulEquiv s.t s.c ∧ RowJ a.x.R.toRealDat a.x.Y.eE s.P.X s.P.inst s.P.G s.t s.S.j := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a F0 s
  have h : StageAt (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y.eE s.P s.S s.t s.c := ⟨s.see, s.ev, s.rowJ⟩
  have e := congrArg (fun p => match p with
    | ⟨_, _, _, _, _, _, _, _, _, R, F, _⟩ => ∀ eE : (w.st Z).toD7.what₂.EE →ₗ[ℂ] R.HE.H, HEq eE t.r.Y.eE →
        StageAt R.toRealDat F.lv2 eE s.P s.S s.t s.c) a.pack
  have key : StageAt a.x.R.toRealDat a.x.F.lv2 a.x.Y.eE s.P s.S s.t s.c := by
    refine e.mpr (fun eE he => ?_) _ a.eE
    obtain rfl : eE = t.r.Y.eE := eq_of_heq he
    exact stageAt_upd _ _ _ _ _ _ _ _ _ _ _ _ _ h
  exact key

end GlobalTheory.Mem.R3.StageMove
