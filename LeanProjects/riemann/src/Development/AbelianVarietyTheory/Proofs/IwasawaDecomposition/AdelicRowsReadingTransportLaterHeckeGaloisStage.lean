import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftTieOfPk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCopy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepOfHeq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.CopyRead

private theorem pin_of {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok}
    {Wt : Set B.places.Pl} {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over} {m : Moved o} {s : Side0 o}
    (r : ReadPk m s) (Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0) (e : r.Y = Y)
    (h8 : ∀ π, (Formalism.IndefR.principalLevelFrame.rowRepR m.z.R.θ (Y.eFT π)).Iso (m.t.rep π))
    (h9 : ∀ x, HEq (Y.Ish.jE x).1 ((m.t.ch true).jE x)) (h10 : ∀ x, HEq (Y.Iz.jE x).1 ((m.t.ch false).jE x))
    (h11 : ∀ i x, HEq (Y.mj.eW i x) (m.t.lf.eW i x)) (h12 : ∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (m.t.lf.jMt μ i x)) : r.Pin := by
  subst e
  exact ⟨h8, h9, h10, h11, h12⟩

private theorem read_pinned {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok}
    {Wt : Set B.places.Pl} {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over} (hF : o.Fits) (m : Moved o) (s : Side0 o)
    (hs : GoodSideLattices.Good m s) : ∃ r : ReadPk m s, r.Pin := by
  have k := read_of_fits B f T w Z₀ hX Wt z₀ q o hF m s
  obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := k
  have k2 := GoodSideLattices.read_of_good hF m s hs Y h9 h10
  obtain ⟨Z⟩ := k2
  exact ⟨⟨Y, Z, h1, h2, h3, h4, h5, h6, h7⟩, pin_of _ Y rfl h8 h9 h10 h11 h12⟩

set_option maxHeartbeats 2000000 in

theorem read_copyN : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I → (∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR) → ∀ (m : Moved (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), m.Copy → m.Coh → ∀ (sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), s.RR = x.s.RR → HEq s.jEE x.s.jEE → (∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd)).coeff (sg.iso g)) → s.cen μ c = x.s.cen μ c0) → ∃ r : ReadPk m s, r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y)  := by
  intro K B f T w P x N hG hGA hCen m hc hco _ s hRR hj _
  have hF : RowPk.Over.Fits (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over) := ⟨x.fits.div, hG, hGA, hCen⟩
  have k := read_pinned hF m s (good_copy x N m hc hco s hRR hj)
  exact k.imp fun r hp => ⟨hp, repOf_heq x.coh x.r x.pin hco r hp⟩

end GlobalTheory.Mem.R3.Rw.CopyRead
