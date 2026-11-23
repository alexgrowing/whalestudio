import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

open Classical in

def cutScale {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y) (x : ℝ) : Scale :=
  S.scale (if x1 < x ∧ x ∈ S.Win then x else y) eps (by split_ifs with h; exacts [hx.trans h.1, hx.trans_le hy]) h0 h1

private theorem cutScale_alt {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (x : ℝ) (h : x1 < x) (hw : x ∈ S.Win) : (cutScale S h0 h1 hx hy x).x = x := if_pos ⟨h, hw⟩

private theorem cutScale_ge {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (x : ℝ) : x1 ≤ (cutScale S h0 h1 hx hy x).x := by
  unfold cutScale Scales.scale
  dsimp only
  split_ifs with h
  exacts [h.1.le, hy]

private theorem cutScale_mem {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (hw : y ∈ S.Win) (x : ℝ) : S.Mem (cutScale S h0 h1 hx hy x) := by
  refine ⟨rfl, ?_⟩
  unfold cutScale Scales.scale
  dsimp only
  split_ifs with h
  exacts [h.2, hw]

theorem Kit.bTopOf_eq {C : FC} {cD ch : ℝ} {s : Scale} (k : Kit C cD ch s) (i i' : k.Ix) :
    bTopOf (k.pt i).L = bTopOf (k.pt i').L := by
  unfold bTopOf
  rw [(k.val i).La_eq, (k.val i').La_eq, k.sc_eq i, k.sc_eq i', (k.same i i').1]

theorem bTopOf_ge {D : D7} (L : SizeData₂ D) (h : L.sc.x ^ L.sc.eps ≤ L.LaG) :
    L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ (2 * L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤ bTopOf L := by
  have hsx : (0 : ℝ) < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hd : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    positivity
  have e : L.sc.x ^ (2 * L.sc.eps) = L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by
    rw [two_mul, Real.rpow_add hsx]
  unfold bTopOf
  rw [e, ← mul_assoc]
  gcongr

def famOfKits {eps : ℝ} (C : FC) (cD ch x1 : ℝ) (hx1 : 1 < x1) (hS : Std C) (hG : C.GK.Nonneg)
    (J : ℝ) (Wn : Set ℝ) (hW : ∀ y : ℝ, ∃ x ∈ Wn, y ≤ x)
    (s : ℝ → Scale) (he : ∀ x, (s x).eps = eps) (hJ : ∀ x, (s x).J = J) (hs : ∀ x, x1 < x → x ∈ Wn → (s x).x = x)
    (k : ∀ x, Kit C cD ch (s x)) (nu : ∀ x i, NumAt C ((k x).pt i).L) : FamP eps where
  x1 := x1
  one_lt_family_threshold := hx1
  Ix x := {_i : (k x).Ix // x ≤ x1 ∨ x ∈ Wn}
  Win := Wn
  Win_unb := hW
  Ix_win x hx := ⟨⟨(k x).ne.some, Or.inr hx⟩⟩
  Ix_zero := ⟨⟨(k 0).ne.some, Or.inl (zero_le_one.trans hx1.le)⟩⟩
  D x i := ((k x).pt i.1).D
  L x i := ((k x).pt i.1).L
  L_x x i hx := by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)]
  L_eps x i := by rw [(k x).sc_eq i.1, he x]
  J := J
  L_J x i := by rw [(k x).sc_eq i.1, hJ x]
  R_eq x i i' := ((k x).same i.1 i'.1).1
  TTn x := ((k x).pt (k x).ne.some).D.host.TT.image Formalism.HC.Frame.A.val
  TT_eq x i := ((k x).same i.1 _).2.1
  realisedChain_torus_eq x i i' := ((k x).same i.1 i'.1).2.2.1
  q_eq x i i' := ((k x).same i.1 i'.1).2.2.2.1
  d_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.1
  QS_eq x i i' := ((k x).same i.1 i'.1).QS_eq
  art_eq x i i' := ((k x).same i.1 i'.1).art_eq
  rd_eq x i i' := ((k x).same i.1 i'.1).rd_eq
  Co := C.P.Cpde
  o_le_Co x i _ := ((k x).val i.1).host.o_le
  QS_le_Co x i _ := ((k x).val i.1).host.QS_le
  g_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.1
  pde_eq x i i' := ⟨((k x).same i.1 i'.1).2.2.2.2.2.2.1, ((k x).same i.1 i'.1).2.2.2.2.2.2.2.1⟩
  W x := (k x).W
  eW x i := (k x).eW i.1
  eW_code x i i' := (k x).eW_code i.1 i'.1
  CGam := C.CGam
  CGam_eq x i := (nu x i.1).CGam_eq
  Cc := C.Cc
  Cc_eq x i := (nu x i.1).Cc_eq
  Ct := C.Ct
  Ct_eq x i := (nu x i.1).Ct_eq
  CT2 := C.CT2
  secondConstant_eq x i := (nu x i.1).secondConstant_eq
  bTop x := bTopOf ((k x).pt (k x).ne.some).L
  bTop_eq x hx i := by
    rw [(k x).bTopOf_eq _ i.1]
    unfold bTopOf
    rw [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)],
      show ((k x).pt i.1).L.sc.eps = eps by rw [(k x).sc_eq i.1, he x]]
  bTop_ge x hx i := by
    rw [(k x).bTopOf_eq _ i.1]
    have h := bTopOf_ge _ (nu x i.1).LaG_ge
    rwa [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)],
      show ((k x).pt i.1).L.sc.eps = eps by rw [(k x).sc_eq i.1, he x]] at h
  bT_le x _ i t := by
    rw [(k x).bTopOf_eq _ i.1]
    exact (nu x i.1).bT_le t
  coverS x _ i0 u0 hu := by
    obtain ⟨i, hi⟩ := (k x).cover_weights i0.1 u0 hu
    exact ⟨⟨i, i0.2⟩, hi⟩
  params x _ i := (nu x i.1).params
  PK := C.PK
  params_K x _ i := (nu x i.1).params_K
  parT x _ i := (nu x i.1).parT
  PT := C.PT
  parT_K x _ i := (nu x i.1).parT_K
  CTu := C.CTu
  sizes x _ i := (nu x i.1).sizes
  ties x i := ((k x).pt i.1).xa.ties
  gatT x i := ((k x).pt i.1).gatT
  X x i := ((k x).pt i.1).xa.X
  Gx x i := ((k x).pt i.1).ta.Gx
  Gy x i := ((k x).pt i.1).ta.Gy
  GK := C.GK
  GK_nonneg := hG
  supp_sat x _ i := ((k x).pt i.1).ta.supp_sat
  tw_supp x _ i := ((k x).pt i.1).ta.tw_supp
  fills x _ i := ((k x).pt i.1).ta.fills
  lats0 x _ i := ((k x).pt i.1).ta.lats0
  latTied x _ i := ((k x).pt i.1).ta.latTied
  Csz := C.Csz
  nuDef x _ i := ((k x).pt i.1).xa.nuDef
  nprimeDef x _ i := ((k x).pt i.1).xa.nprimeDef
  rrDef x _ i := ((k x).pt i.1).xa.rrDef
  h_eq x _ i := ((k x).pt i.1).xa.h_eq
  cX := C.cX
  ex x _ i := ((k x).pt i.1).xa.ex
  rho_le x hx i := by
    have h := (nu x i.1).rho_le
    rwa [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)]] at h
  Cr := C.Cr
  one_le_Cr := hS.1.2.2.2.2.2.2.1.ge
  drop_iff x _ i := ((k x).pt i.1).ta.drop_iff
  fixed := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, _⟩ := hS.1
    exact ⟨a1, a2, a3, a4, a5, a6, a7, fun x _ i => ⟨(nu x i.1).CnW_eq.trans a8, (nu x i.1).eP_eq ▸ a9⟩⟩
  eta_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.1
  Sc_shared x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.1
  hP_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.1
  bs_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.1
  off_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.1
  kapI_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  ep_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem exists_famP_of_kits : ∀ (eps : ℝ) (C : FC) (cD ch x1 la : ℝ) (S : Scales la), 0 < eps → eps < 1 / 52 → 1 < x1 → 1 ≤ la → Std C → C.GK.Nonneg → ∀ k : ∀ s : Scale, s.eps = eps → x1 ≤ s.x → S.Mem s → Kit C cD ch s, (∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L)) → ∃ Fm : FamP eps, Fm.x1 = x1 ∧ Fm.cPre = C.cPre ∧ Fm.cOut = C.cOut.set 15 C.P.Cpde ∧ Fm.cMid = C.cMid ∧ Fm.cLast = C.cLast ∧ Fm.CTu = C.CTu ∧ (∀ Q : PtProp, (∀ s h h' h'' i, ((k s h h' h'').pt i).Has Q) → classOf Q Fm) ∧ (∀ Rr : ∀ (D : D7) (L : SizeData₂ D), G.Inst D L → Prop, (∀ s h h' h'' i, Rr ((k s h h' h'').pt i).D ((k s h h' h'').pt i).L ((k s h h' h'').pt i).ta.Gx) → ∀ x, ∀ i : Fm.Ix x, Rr (Fm.D x i) (Fm.L x i) (Fm.Gx x i)) ∧ Fm.J = S.J ∧ Fm.Win = S.Win ∧ Fm.Co = C.P.Cpde := by
  intro eps C cD ch x1 la S h0 h1 hx hla hS hG k hN
  obtain ⟨y, hw, hy⟩ := S.unb hla x1
  have hJ : S.J ≤ C.P.Cpde := by
    have k0 := k (cutScale S h0 h1 hx hy 0) rfl (cutScale_ge S h0 h1 hx hy 0) (cutScale_mem S h0 h1 hx hy hw 0)
    have h := (k0.val k0.ne.some).host.J_le
    rwa [k0.sc_eq] at h
  refine ⟨famOfKits C cD ch x1 hx hS hG S.J S.Win (S.unb hla) (cutScale S h0 h1 hx hy) (fun _ => rfl) (fun _ => rfl)
    (cutScale_alt S h0 h1 hx hy)
    (fun x => k (cutScale S h0 h1 hx hy x) rfl (cutScale_ge S h0 h1 hx hy x) (cutScale_mem S h0 h1 hx hy hw x))
    (fun x i => (hN _ _ _ _ i).some),
    rfl, rfl, ?_, rfl, rfl, rfl, fun Q hQ x _ i => hQ _ _ _ _ i.1, fun Rr hR x i => hR _ _ _ _ i.1, rfl, rfl, rfl⟩
  rw [← congrArg (C.cOut.set 15) (max_eq_left hJ)]
  rfl

end GlobalTheory.EX

end
