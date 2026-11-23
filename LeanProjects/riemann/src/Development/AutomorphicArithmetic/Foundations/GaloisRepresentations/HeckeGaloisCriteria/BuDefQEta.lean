import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

namespace UpperTheory.GalC.Gen

open Formalism.BasicNotions Formalism.MainNotions NumberField
open GlobalTheory.HeightCounting

structure Raw (D : D7) where
  η : ℕ → D.what₂.places.Pl → ℚ
  hη : ∀ j w, 0 ≤ η j w
  P : @NLay0 D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0
  hZ : @NLay0.ZOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P
  hE : @NLay0.EtaOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P

@[reducible] def Raw.rec' {D : D7} (Λ : Raw D) : D7 := setRaw D Λ.η Λ.hη Λ.P Λ.hZ Λ.hE

variable {D : D7} (Λ : Raw D)

set_option maxHeartbeats 1600000

@[reducible] def ledTr (L : SizeData₂ D) : SizeData₂ Λ.rec' := { L with }

@[reducible] def instTr {L : SizeData₂ D} (X : G.Inst D L) : G.Inst Λ.rec' (ledTr Λ L) := { X with }

@[reducible] def gatTr (x : GatTies D) : GatTies Λ.rec' := { x with }

@[reducible] def latTr (x : G.LatInst D) : G.LatInst Λ.rec' := { x with }

@[reducible] def cmpTr (x : LatCmp D) : LatCmp Λ.rec' := { x with }

@[reducible] def twTr (x : TwForms D) : TwForms Λ.rec' := { x with }

@[reducible] def thTr (x : ThetaX D) : ThetaX Λ.rec' := { x with }

@[reducible] def errTr (x : ErrX D) : ErrX Λ.rec' := { x with }
open DivX (md) in

@[reducible] def divTr (X : DivX D) : DivX Λ.rec' := { X with md := fun S κ p _ la z => { md X S κ p la z with } }
section Local

variable {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ) (p j : ℕ)

theorem VV_tr : G.VV (instTr Λ X) K a b p = G.VV X K a b p := by
  have e1 : G.Cand _ (ledTr Λ L) K p = G.Cand D L K p := rfl
  have e2 : G.goodReps (instTr Λ X) p = G.goodReps X p := rfl
  have e3 : G.Sig (instTr Λ X) K a b p = G.Sig X K a b p := rfl
  unfold G.VV; rw [e1, e2, e3]; rfl

theorem tau_translate : G.tauP (instTr Λ X) K a b p = G.tauP X K a b p := by
  unfold G.tauP; rw [VV_tr]; rfl

theorem ioP_instTr : G.ioP (instTr Λ X) K a b p = G.ioP X K a b p := by
  unfold G.ioP; rw [VV_tr]; rfl

theorem gainP_instTr : G.gainP (instTr Λ X) K a b p j = G.gainP X K a b p j := by
  unfold G.gainP; rw [VV_tr]; rfl

theorem TTP_tr : G.TTP (instTr Λ X) K a b p = G.TTP X K a b p := by
  unfold G.TTP; rw [VV_tr]; rfl

theorem fills_tr (w : D.what₂.places.Pl) (H : G.ParametersFill X K w) : G.ParametersFill (instTr Λ X) K w :=
  ⟨H.1, H.2.1, H.2.2.1.trans (TTP_tr Λ X K _ _ _).symm,
    fun h1 h2 j hj => (H.2.2.2.1 h1 h2 j hj).trans (gainP_instTr Λ X K _ _ _ _).symm,
    H.2.2.2.2.1.trans (tau_translate Λ X K _ _ _).symm, H.2.2.2.2.2.1.trans (ioP_instTr Λ X K _ _ _).symm, H.2.2.2.2.2.2⟩

theorem NP_tr (Y : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    G.NP (instTr Λ X) (latTr Λ Y) K u w hg = G.NP X Y K u w hg := by
  have e0 : G.aL (ledTr Λ L) = G.aL L := rfl
  have e1 : G.bL (ledTr Λ L) = G.bL L := rfl
  have e2 : ∀ a b p t, G.Sv (instTr Λ X) K a b p t = G.Sv X K a b p t := fun _ _ _ _ => rfl
  unfold G.NP
  simp only [e0, e1, e2, VV_tr, tau_translate]
  rfl

end Local

def extraTr {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
    (ex : Extra D L gatT Gx Gy K X cX) (nch : NChoice Λ.rec') (tie : NChTie Λ.rec' nch) (xd : ThData Λ.rec')
    (p0 : BaseLevelRowSide Λ.rec') (rr0 : p0.s.RRDef) (amb : AmbForm Λ.rec' (RowSide.sharp Λ.rec')) (amb0 : AmbForm Λ.rec' p0.s)
    (ks : kapSharp Λ.rec' = kapSharp D) :
    Extra Λ.rec' (ledTr Λ L) (gatTr Λ gatT) (instTr Λ Gx) (latTr Λ Gy) K (divTr Λ X) cX where
  lev := ex.lev
  th := thTr Λ ex.th
  th_io := ex.th_io
  cmp := cmpTr Λ ex.cmp
  lat := ⟨ex.lat.vram, fun u w hg hv x => by
    erw [NP_tr]; exact ex.lat.served u w hg (by rw [← VV_tr Λ]; exact hv) x, ex.lat.atT⟩
  tw := twTr Λ ex.tw
  ker := fun u w g => { ex.ker u w g with }
  ep_def := ex.ep_def
  ep_tie := ex.ep_tie
  kapI_def := ex.kapI_def
  fills_all := ex.fills_all
  nu_unserved := fun u w h1 h2 => ex.nu_unserved u w h1 (by rw [← VV_tr Λ]; exact h2)
  idx := { ex.idx with }
  kap_def := ex.kap_def
  lam_def := ex.lam_def
  kapR_def := ex.kapR_def.trans ks.symm
  errX := errTr Λ ex.errX
  err := { ex.err with }
  nch := nch
  nch_tie := tie
  xd := xd
  p0 := p0
  rationalRoots_def := rr0
  amb := amb
  amb0 := amb0
  fdef := ex.fdef
  duStar_def := ex.duStar_def
  Dstar_def := ex.Dstar_def
  gauge := ex.gauge
  gauge_def := ex.gauge_def

@[reducible] def parTr {L : SizeData₂ D} (P : ParameterChoice' D L) : ParameterChoice' Λ.rec' (ledTr Λ L) := { P with }

@[reducible] def parTTr {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : ParamsT Λ.rec' (ledTr Λ L) (parTr Λ P) := { T with }

set_option smartUnfolding false in
theorem buDefQ_eta (h : Rows.BuDefQ D.what₂) : Rows.BuDefQ (rowsEta D.what₂ Λ.η Λ.hη) := by
  have e : (rowsEta D.what₂ Λ.η Λ.hη).sec D.what₂.mu0 = D.what₂.sec D.what₂.mu0 := by
    first
      | rfl
      | with_unfolding_all rfl
  intro u φ x
  have := h u φ x
  rw [← e] at this
  exact this

theorem tiesTr (h : Ties D) (k : TwCoverPair Λ.rec') : Ties Λ.rec' := { h with bu_def := buDefQ_eta Λ h.bu_def, tw_cover := k }

set_option smartUnfolding false in
theorem rrDefTr (h : DV.RRDef D) : DV.RRDef Λ.rec' := by
  have e : (rowsEta D.what₂ Λ.η Λ.hη).RRset = D.what₂.RRset := by
    first
      | rfl
      | with_unfolding_all rfl
  intro x
  have := h x
  rw [← e] at this
  exact this

end UpperTheory.GalC.Gen
