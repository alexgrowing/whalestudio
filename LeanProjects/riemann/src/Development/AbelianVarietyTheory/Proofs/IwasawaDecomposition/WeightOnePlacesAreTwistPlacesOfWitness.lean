import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPins3RealTOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqClosedContentNumericalDatum
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

theorem finite_T_of_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L}
    {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC}
    {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX} {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) : Finite a.x.T := by
  have hfin : Finite (TupU w.I (usedOf w.I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T Wt)).finite_toSet
    exact hs.to_subtype
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hfin

set_option maxHeartbeats 4000000 in

theorem zscale_f0_of_witness {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b) (hsc : q.O.L.sc = K.s) :
    HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  have hK : DV.KapDef (q.w.D q.Z) := b.R.T.what₂.ka
  have hB : ∀ Zs, HEq ((rpkB b).Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := by
    intro Zs
    apply heq_of_eq
    funext y j
    rw [← hsc]
    exact (forcedContent_eq_closedContent_numericalDatum _ _ _ _ hK y j).symm
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  have hX := y.eq ▸ hB
  letI := a.x.grp
  letI := a.x.fin
  have hX' : ∀ Zs : DefSub a.x.A3.fam3.amb3, HEq (a.x.F.Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := hX
  dsimp only
  clear * - hX'
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x', pack, _⟩ := a
  dsimp only at hX' ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x'
  dsimp only at pack hX' ⊢
  cases pack
  exact hX' _

set_option maxHeartbeats 4000000 in

theorem weight_one_places_are_twist_places_of_witness : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) (K : Ctx) (q : WPt p.s K) (c : ℝ)
    (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c), BWit q b → q.O.L.sc = K.s →
    (∀ v, (b.B.Q.Rl.toCx3 b.B.Q.F).W1 b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F 0 0) v → v ∈ b.B.Q.Rl.twPl) ∧
      b.B.Q.Rl.toRealDat.ExAt ∧ Finite b.P.T := by
  intro hL p K q c b w hsc
  have hZ := zscale_f0_of_witness q b w hsc
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  letI := a.x.grp
  letI := a.x.fin
  letI : Algebra (↥a.x.core.Q.c.F) (q.w.D q.Z).what₂.LL := a.x.alg
  have h3 : RealPins3 (realTOf y.y) :=
    realPins3_realTOf K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a b.R b.S y.y hZ
  have hP : (fun r : RPk b.R b.S => RealPins3 r.B.Q ∧ r.B.Q.Rl.toRealDat.ExAt ∧ Finite r.P.T) (rpkX y.y) :=
    ⟨h3, y.intersectionNumber_baseChange.aux.ex, finite_T_of_twArgs a⟩
  rw [← y.eq] at hP
  exact ⟨hP.1.w1 0 0, hP.2.1, hP.2.2⟩

end GlobalTheory.Mem.Top.Bl

end
