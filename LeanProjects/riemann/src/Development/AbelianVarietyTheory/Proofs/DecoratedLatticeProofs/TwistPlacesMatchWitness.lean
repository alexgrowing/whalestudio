import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopReadOfTrueQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

private noncomputable def packK {D : D7} {O : Obj D} {R : Formalism.L2.RecT O.ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} (k : Bl.RPk R S) :
    RealPack O.ex :=
  letI := k.B.alg
  { R := R, S := S, P := k.P, Dcf := k.Dc, Spf := k.Sp, Zscf := k.Zsc, Ks := k.B.T.Q.c.F, Q := k.B.Q }

set_option maxHeartbeats 2000000 in

theorem qplaces_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ t PP, PP ∈ (pk (packB b)).Q t ↔ PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (b.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K) := by
  intro hL p K q c b hw
  obtain ⟨x, a, ax, y, -, -, -, -, -, -, -, -, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  subst hx
  have main : ∀ t PP, PP ∈ (pk (packK (Bl.rpkX y.y))).Q t ↔
      PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup ((Bl.rpkX y.y).P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K) := by
    intro t PP
    obtain ⟨-, -, hl, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
    have h1 := (hl _ (Inhab.packOf_tup y.y t).1).1
    rw [(Inhab.packOf_tup y.y t).2] at h1
    exact Iff.of_eq (congrArg (PP ∈ ·) (eq_of_heq h1))
  show (fun k : Bl.RPk b.R b.S => ∀ t PP, PP ∈ (pk (packK k)).Q t ↔
      PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (k.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K)) (Bl.rpkB b)
  rw [y.eq]
  exact main

end GlobalTheory.Fam
