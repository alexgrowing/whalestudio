import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq

noncomputable section

namespace GlobalTheory.Mem.Top.V4

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

structure RowLay (D : D7) (p0 : BaseLevelRowSide D) (X : DivX D) : Prop where
  rrDef : DV.RRDef D
  rationalRoots_def : p0.s.RRDef
  kap_def : DV.KapDef D
  lam_def : DV.LamDef D
  bu_def : Rows.BuDefQ D.what₂
  ft_occ : ∀ π, (∃ σ, D.what₂.ft σ = π) ∨ ∃ σ, D.what₂.ft0 σ = π
  untw : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m →
    D.what₂.Ij D.what₂.mu0 j w = 0 ∧ D.what₂.jw D.what₂.mu0 j w = 0
  idx : IdxDefs D X
  kapR_def : DV.KapRBase X

structure MuIsW (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl) (xi : X.C.Tup → HChar X.B.host.E) : Prop where
  inj : Function.Injective xi
  range : Set.range xi = T.set f
  mu0 : xi X.C.mu0 = 1
  star : xi X.C.muStar = f.del
  star' : xi X.C.muStar' = f.del'
  tw : ∀ w, xi (X.W.muTw w) = T.xiTw f w
  on : ∀ w, w ∈ Wt → X.W.muAt w = X.W.muTw w
  off : ∀ w, w ∉ Wt → X.W.muAt w = X.C.mu0
  sub : ∀ w ∈ Wt, X.B.places.resChar w ∈ T.pl
  supp : ∀ w, w ∉ Wt → T.psi w = 1

theorem muIsW_of_muIs {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {xi : X.C.Tup → HChar X.B.host.E} (h : MuIs X f T xi) :
    MuIsW X f T {w | X.B.places.resChar w ∈ T.pl} xi :=
  ⟨h.inj, h.range, h.mu0, h.star, h.star', h.tw, h.on, h.off, fun _ hw => hw, fun w hw => (T.off w hw).1⟩

structure Core (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) : Type 1 where
  isOver : K.Over X.B.toPre
  xi : X.C.Tup → HChar X.B.host.E
  Wt : Set X.B.places.Pl
  mu : MuIsW X f T Wt xi
  forced : ∀ p : ℕ, p.Prime → ((∃ i, p = X.B.host.g i) ∨ p = X.B.host.d ∨ (p : ℝ) ≤ K.s.X'' X.B.R.n) → p ∈ T.pl
  fval : ∀ L : SizeData₂ X.toD7, L.sc = K.s → WtEq L K.a K.b → Val K.C K.cD K.ch L → ∀ w, w ∉ Wt →
    ∀ j ∈ SizeData₂.lifts X.toD7, Fval L j w = 0
  O : Obj2 X.toD7
  col : ColLay X.toD7 O.lev O.errX
  gatNum : GatNum K.s X.toD7
  gy : GyLay K X.toD7 O.gatT O.cmp O.Gy
  row : RowLay X.toD7 O.p0 O.X
  mtStable : DQ.MtStableAt X.toD7
  th_io : O.th.TieIo
  gauge_def : letI := X.toD7.host.cmStar; O.gauge.IsGauge
  real : Formalism.L2.Theta.RealTied X.toD7
  dsig_eq : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)
  del : X.S.s.Del = (Delv K.s K.cD : ℚ)
  etaF : X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  chiT : ∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
    ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))
  nch_tie : NChTie X.toD7 O.nch
  nch_Q : ∀ w ∈ Wt, O.nch.Q w = T.Q w ∧ O.nch.k' w = T.k w

abbrev Slot : Type 1 := ∀ (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B), Core K X f T → Prop

structure KsCond (KP : ∀ B : Base, Fr B.toPre → Prop) : Prop where
  ex : Ev fun K => ∀ (B₀ : Base) (f₀ : Fr B₀.toPre) (S₁ : IntermediateField ℚ ℂ → Finset ℂ)
    (S₂ : IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℂ), K.Over B₀.toPre → (∀ F, ∀ z ∈ S₁ F, IsAlgebraic ℚ z) →
    (∀ F F₀, ∀ z ∈ S₂ F F₀, IsAlgebraic ℚ z) →
    ∃ (B : Base) (f : Fr B.toPre), B.toPre = B₀.toPre ∧ HEq f f₀ ∧ KP B f ∧ Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex)
  enl : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre), Enl B B' → HEq f' f → KP B f → KP B' f'

def ExTrue (KP : ∀ B : Base, Fr B.toPre → Prop) (Q : Slot) : Prop :=
  EvLg fun K B f T => KP B f → ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W) (G : GJStage B C)
    (c : Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c

def Export (Q : Slot) : Prop :=
  Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : Core K X f T), Q K X f T c → ExportAt X.toD7 c.O.nch c.O.xd

def Retwist (Q Q' : Slot) : Prop :=
  Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : Core K X f T), Q K X f T c → ExportAt X.toD7 c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ B : Pre, Fr B → Set (HChar B.host.E) → Finset ℂ), (∀ B f Ξ, ∀ z ∈ S₂ B f Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl X.B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧
        ∀ (C : Cols B') (W : RowsRest B' C) (V : DivStage B' C W) (S : SStage B' C W) (N : NStage B' C W) (G : GJStage B' C)
          (c' : Core K ⟨B', C, W, V, S, N, G⟩ f' T'), Q K ⟨B', C, W, V, S, N, G⟩ f' T' c' →
          DQ.TwAllAt (assemble B' C W V S N G) c'.O.nch c'.O.xd ∧ Q' K ⟨B', C, W, V, S, N, G⟩ f' T' c'

def FromCore (Q : Slot) (D : D7) (Y : Lay D) : Prop :=
  ∃ (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : Core K X f T), Q K X f T c ∧
    (⟨D, layObj Y⟩ : Σ D : D7, Obj2 D) = ⟨X.toD7, c.O⟩

end GlobalTheory.Mem.Top.V4

end
