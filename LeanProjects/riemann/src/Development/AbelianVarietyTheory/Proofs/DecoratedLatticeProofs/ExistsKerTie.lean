import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTrueWith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BuiltCols
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedWithEnt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfIsAllOfSame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ErrXSPiAndVal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC

section BaseLevels₂

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Core.DefKer.stdRd_keep {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hS : I.StdKer l Z t) :
    ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ t'.O = t.O ∧ t'.ent = t.ent := by
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, rfl, rfl⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Core.DefKer.all_pins {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (hTw : I.IsTw) (l : I.Laws)
    (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX)
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw) (hQ : I.QpIs Y.Qp)
    (hO : I.StdO l Z Y.Qp O) (hU : ∀ u a i, i < B.R.m → UnfIsAll (O u a) i) (hE : EntOk E O)
    (hS : ∀ u w h, ThAtServed (ex.ker u w h) E)
    (hC : ∃ (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)) (h : KerEntHyp Pl O Bs Y ex.tw), E = kerEntC Pl O Bs h)
    (hpi : ex.errX.piT = X.piT) :
    ∃ t : KerEntTied ex, I.StdKer l Z t ∧ GlobalTheory.Pdv.StdRd I l Z t ∧ GlobalTheory.Pdv.IsEntC t ∧ t.Adapted ∧ t.TopPinned ∧ t.AAUnit ∧ t.UnfAll ∧
      t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  obtain ⟨t1, s1, o1, -, p1⟩ := kerEntTied_true I hOk hP l Z L hT Gi Gl K Y cX ex O E hQ hO hU hE hS
  obtain ⟨t0, s0, o0, e0, a0, -⟩ := kerEntTied_withEnt I l Z O E hE hS t1 s1 o1 p1
  obtain ⟨t, s, r, p, o, e⟩ := GlobalTheory.Core.DefKer.stdRd_keep I hOk l Z t0 ((StdModel.stdKer_iff I l Z t0).2 s0)
  obtain ⟨k1, k2⟩ := kernel_inputs I hOk hP l Z L hT Gi Gl K Y cX ex t s p hTw
  obtain ⟨c1, c2, c3, c4⟩ := k_pins_tie I hOk hP l Z L hT Gi Gl K Y cX ex t ((StdModel.stdKer_iff I l Z t).1 s) hpi
  refine ⟨t, s, r, ?_, ?_, p, k1, k2, c1, c2, c3, c4⟩
  · unfold GlobalTheory.Pdv.IsEntC
    rw [o, e, o0, e0]
    exact hC
  · unfold KerEntTied.Adapted at a0 ⊢
    rw [o, e]
    exact a0

end BaseLevels₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Core GlobalTheory.Core.Cls NumberField IsDedekindDomain GlobalTheory.Mem.Db Formalism.L2 Formalism.L2.Ker Formalism.L2.Forms

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Core.DefKer.exists_kerTie : ∀ (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z) (O : Obj (w.D Z)), ofObj O = b.obj → ∃ t : KerEntTied O.ex, TC.StdKer w.I w.l Z t ∧ GlobalTheory.Pdv.StdRd w.I w.l Z t ∧ GlobalTheory.Pdv.IsEntC t ∧ t.Adapted ∧ t.TopPinned ∧ t.AAUnit ∧ t.UnfAll ∧ t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  intro K B f T w Z b O hO
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  simp only [ofObj, extraObj, CoreB.obj, Obj2.mk.injEq] at hO
  obtain ⟨h1, -, h3, h4, h5, h6, -, -, -, h10, -, h12, -⟩ := hO
  subst h1 h3 h4 h5 h6 h10
  obtain rfl := eq_of_heq h12
  exact GlobalTheory.Core.DefKer.all_pins w.I w.ok w.pins b.pin.isTw w.l Z _ b.kt.O b.kt.E b.sd.qp b.kt.std b.kt.unf b.kt.ok b.kt.served b.entC
    (GlobalTheory.Core.Cls.errXS_pi_and_val K B f T w Z b).2.1
