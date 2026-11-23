import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPinsRealTOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSpacesOfOver

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LinkedPins

set_option maxHeartbeats 4000000 in

theorem seeAt_twArgs {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf (w.st Z).toD7) (s : Formalism.L2.Theta.GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0))
    (hs : SeeAt (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 X h s) : SeeAt a.x.R.toRealDat a.x.F.lv2 X h s := by
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  refine ⟨hs.fin, ?_, ?_⟩
  · exact (hs.conj)
  · exact (hs.mat)

theorem setting_congr {D : D7} (M : ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Prop)
    {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (e : F0 = F0') {P : SPack D F0} {P' : SPack D F0'} (hP : HEq P P')
    (h : M P'.X P'.inst) : M P.X P.inst := by
  subst e
  cases hP
  exact h

set_option maxHeartbeats 4000000 in

theorem realPins_of_seeAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} {x : TwIn ex} {Rc : Formalism.L2.RecT ex}
    {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} (y : RealIn x Rc S) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (sS : SRest P)
    (e : S = sS.toSTiesR Rc) (hC : x.R.C = Rc.T.n.cf) (hD : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i))
    (hPg : open Classical in x.R.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE))
    (hs : SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS) : RealPins (realTOf y) := by
  subst e
  have hι : y.ιS = (iotaX P.X P.inst).toMulEquiv := ((JIota.heq_iota_iff D P.X P.inst y.ιS).mp y.ιS_eq)
  refine realPins_realTOf _ _ _ _ _ _ _ _ ex x Rc _ y hC hD hPg hs.fin ?_ ?_
  · rw [hι]
    exact (hs.conj)
  · exact (hs.mat)

open Classical in

theorem image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {Pr : Formalism.L2.Col.Primes X} {Pr' : Formalism.L2.Col.Primes X'} (hP : HEq Pr Pr') :
    Pr.vGs.image (Formalism.L2.Host.CT.plMap s.iE) = Pr'.vGs.image (Formalism.L2.Host.CT.plMap s'.iE) := by
  subst hX
  cases hs
  cases hP
  rfl

open Classical in

theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  have h : Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id := by
    funext P
    ext x
    exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x
  rw [h, Finset.image_id]

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

set_option maxHeartbeats 4000000 in

theorem realPins_wit (q : WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c) (w : BWit q b) : RealPins (realTOf w.y.y) := by
  obtain ⟨x, a, ax, y, recPin, ⟨sP, sS, hP, -, e⟩, ⟨pt, -⟩, _⟩ := w
  cases ax
  obtain ⟨h1, h2, -⟩ := twArgs_lev _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have hk := recPin.k.std
  have fd : ∀ V : Formalism.BasicNotions.TH.HSp (q.w.D q.Z), GlobalTheory.Mem.HostFrames.SignFrame V → IsFDiag V := fun V hV => by
    obtain ⟨d, -, h⟩ := hV.gram_eq (q.w.D q.Z).host.F
    exact ⟨d, h⟩
  have hWV := (GlobalTheory.Mem.HostFrames.frames_of_over K (q.w.st q.Z) q.x.isOver).2.1
  refine realPins_of_seeAt y.y sS e ?_ (fun i => ⟨fd _ (hWV i).1, fd _ (hWV i).2⟩) ?_ ?_
  · have hc : b.R.T.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst recPin.s.chr
    have hC : Top.Fr.at (q.w.st q.Z) q.w.I.C = Top.Fr.at (q.w.st q.Z) q.f := congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq
    exact (eq_of_heq h1).trans (hC.symm.trans hc.symm)
  · rw [image_congr hk.X_eq hk.seam hk.Pr]
    exact (eq_of_heq h2).trans (image_refl _ rfl _).symm
  · have ht : y.y.tS = q.sat.t := eq_of_heq pt
    have hcols : b.R.T.cols = q.x.col.C := recPin.s.cols
    rw [ht]
    exact seeAt_twArgs a sP.X sP.inst q.sat.t (setting_congr (D := (q.w.st q.Z).toD7)
      (fun X h => SeeAt (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2 X h q.sat.t)
      (congrArg (fun C u => (C.forms u).to0) hcols) hP q.sat.see)

end GlobalTheory.Fam.LinkedPins

open GlobalTheory.MiS GlobalTheory.Fam in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Fam.realPins_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → Formalism.IndefR.RealPins b.B.Q := by
  intro hL p K q c b w
  show (fun k : Bl.RPk b.R b.S => Formalism.IndefR.RealPins k.B.Q) (Bl.rpkB b)
  rw [w.y.eq]
  exact GlobalTheory.Fam.LinkedPins.realPins_wit q b w
