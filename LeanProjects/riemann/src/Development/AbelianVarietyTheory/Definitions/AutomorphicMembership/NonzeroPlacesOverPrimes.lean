import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical in

def FK (s : Scale) (D : D7) (j p : ℕ) : ℝ :=
  if ∃ i, p = D.host.g i then FTypeG D j
  else if D.host.cls p = PrimeClass.ramD then FRamD D j
  else if (G.IsResidueClassZero D p ∨ G.IsSg D p) ∧ (p : ℝ) ≤ s.X'' D.R.n then FInert D j p
  else 0

def F0K (s : Scale) (D : D7) (y : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) : ℝ :=
  FK s D (j.1 + 1) (D.what₂.places.resChar (D.plEq.symm y))

section Reading

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def MjAre (Z : R3.ReadL R F X0 Y) (Xd : DivX D) : Prop :=
  ∃ J : MjHIds D A3.A Xd (A3.indefDown (R3.s0Of R F)), MjHTie D A3.A Xd (A3.indefDown (R3.s0Of R F)) Z.jW J

def AmbAre (_Z : R3.ReadL R F X0 Y) (a : AmbForm D (RowSide.sharp D)) (a0 : AmbForm D X0.s) : Prop :=
  (∃ J, AmbTie D A3.A (RowSide.sharp D) a F.P1 F.ψ1 Y.tup Y.jA J) ∧ ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 Y.tup Y.jA0 J

end Reading

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure RowsT (K : Ctx) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) : Type 1 where
  hX : B.fields.Ok
  r : R3.RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0
  exAt : r.z.R.toRealDat.ExAt
  inGeo : GlobalTheory.RealGeo.InGeo r.z.geo
  grpAt : R3.GrpAt (w.st Z) w.I
  grp : GrpTrue Z.N f
  mu : V4.MuIsW (w.st Z) f T Wt w.I.xi
  exact : Wt = r.z.W1 (F0K K.s (w.D Z))
  untw : ∀ v, v ∉ Wt → ∀ j, 1 ≤ j → j ≤ B.R.m → (w.D Z).what₂.Ij (w.D Z).what₂.mu0 j v = 0 ∧ (w.D Z).what₂.jw (w.D Z).what₂.mu0 j v = 0
  emt0 : ∀ u F G, inner ℂ ((w.D Z).eMt u F) ((w.D Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G
  emt : ∀ u (a : (w.D Z).what₂.Tup), a ≠ (w.D Z).what₂.mu0 → ∀ F G,
    inner ℂ ((w.D Z).eMtTw u a F) ((w.D Z).eMtTw u a G) = TC.ipMt w.I w.l u a F G
  etaF : Z.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  rowInt : GlobalTheory.PerQ.RowInt w.I w.l Z
  idx : ∀ Y : DivX (w.st Z).toD7, MjAre r.Z Y → IdxDefs (w.D Z) Y

structure ObjT {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} (O : Obj2 (w.D Z)) (t : RowsT K w Z Wt O.p0) : Prop where
  amb : AmbAre t.r.Z O.amb O.amb0
  mjH : MjAre t.r.Z O.X
  kapR : ∀ σ, O.X.kapR σ = kapSharp (w.D Z)

def DatGood : WP := fun K B f T w =>
  ∃ (Z : w.Lt) (hX : B.fields.Ok) (z : R3.Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}),
    GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ R3.GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) ∧ z.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z.geo ∧
    (Formalism.L2.Pj.LawsCore z.core.toCore ∧ z.core.Q.Canon ∧ (∀ j, 1 ≤ (z.core.Q.Dw j).p + (z.core.Q.Dw j).q) ∧ z.core.pb = f.P.pb) ∧
    z.Std ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧ ∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1

def Supp : WP := fun K B f T w => T = TwDat.untw B T.pl ∨ DatGood K B f T w

structure Coh (B : Base) (T : TwDat B) : Prop where
  same : ∀ v v', (∀ x ∈ B.LL0, 0 ≤ B.places.val v x ↔ 0 ≤ B.places.val v' x) → T.Q v = T.Q v' ∧ T.k v = T.k v' ∧ T.psi v = T.psi v'
  roots : ∀ v, ∃ z : B.LL, IsPrimitiveRoot z (B.places.resChar v ^ T.k v)

def Start : WP := fun K B f T w => Pinned K B f T w ∧ Supp K B f T w ∧ Coh B T

def DatEx : Prop := StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok), GrpTrue Z.N f → R3.GrpAt (w.st Z) w.I →
  ∃ z : R3.Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}, z.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z.geo

def UnitaryCaseCondition : Prop := StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt →
    GlobalTheory.RealGeo.InGeo z.geo → R3.Holds z.R z.F

def NonzeroPlacesOverPrimes : Prop := StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → R3.GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) →
    R3.Holds z.R z.F → ∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl

def Below (D D' : D7) (v : D.what₂.places.Pl) (v' : D'.what₂.places.Pl) : Prop :=
  ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
    (x ∈ (D.plEq v).asIdeal ↔ x' ∈ (D'.plEq v').asIdeal)

def NonzeroPlacesInvariant : Prop := StepW Pinned fun K B f T w => ∀ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B') (w' : ColW B' f' T'), Enl B B' →
  HEq f' f → Pinned K B' f' T' w' → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ →
  ∀ (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (z' : R3.Dat (w'.st Z') w'.I hX' T' Wt'),
    GrpTrue Z.N f → R3.GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → GrpTrue Z'.N f' → R3.GrpAt (w'.st Z') w'.I → DV.KapDef (w'.D Z') →
    R3.Holds z.R z.F → R3.Holds z'.R z'.F →
    ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (F0K K.s (w.D Z)) ↔ v' ∈ z'.W1 (F0K K.s (w'.D Z')))

abbrev NCondition : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (_ : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (_ : ThData (w.D Z)), Type 1

abbrev SPosition : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (_ : RowsT K w Z Wt p0) (_ : ColT w Z), Type 1

abbrev OComponent₂ : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (O : Obj2 (w.D Z)) (_ : RowsT K w Z Wt O.p0), Type 1

abbrev RPosition : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (_ : RowsT K w Z Wt p0), Type 1

structure Slots : Type 2 where
  Rx : RPosition
  Nx : NCondition
  Sx : SPosition
  Ox : OComponent₂

structure Lv2 (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 where
  g : GIs2 K w Z.G
  coh : Coh B T
  Wt : Set B.places.Pl
  p0 : BaseLevelRowSide (w.D Z)
  what₂ : RowsT K w Z Wt p0
  rx : 𝒮.Rx K B f T w Z Wt p0 what₂

structure Lv3 (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 extends Lv2 𝒮 K w Z where
  nch : NChoice (w.D Z)
  n : NchT w Z Wt nch
  xd : ThData (w.D Z)
  chiT : ∀ (k : Fin 2) (v : Z.N.nd.PlG k), ∃ x : (ZMod (B.host.g k))ˣ, orderOf x = B.host.g k - 1 ∧
    ∀ j : Fin B.R.m, Z.N.nd.chiT k v j = x ^ (2 * (j.1 + 1))
  nx : 𝒮.Nx K B f T w Z Wt p0 what₂ nch n xd

structure Lv4 (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 extends Lv3 𝒮 K w Z where
  col : ColumnDataSplitPrimes K w Z
  real : Formalism.L2.Theta.RealTied (w.D Z)
  dsig_eq : ∀ τ, Z.S.dsig τ = Vol.trueDsig B.R (B.hc τ)
  del : Z.S.s.Del = (Delv K.s K.cD : ℚ)
  sx : 𝒮.Sx K B f T w Z Wt p0 what₂ col.toColT

structure Built (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) (c : V4.Core K (w.st Z) f T) : Type 1 where
  pin : ColPin w
  coh : Coh B T
  g : GIs2 K w Z.G
  col : ColumnDataSplitPrimes K w Z
  what₂ : RowsT K w Z c.Wt c.O.p0
  rx : 𝒮.Rx K B f T w Z c.Wt c.O.p0 what₂
  xi : c.xi = w.I.xi
  lev : c.O.lev = col.full.1.base.lev0
  errX : c.O.errX = Formalism.L2.Herm.toErrXS col.full.1
  n : NchT w Z c.Wt c.O.nch
  nx : 𝒮.Nx K B f T w Z c.Wt c.O.p0 what₂ c.O.nch n c.O.xd
  sx : 𝒮.Sx K B f T w Z c.Wt c.O.p0 what₂ col.toColT
  ker0 : KerFam (w.D Z) col.Gt col.cmp (w.tw Z) c.O.Gy
  ker_eq : (⟨c.O.gatT, c.O.cmp, c.O.tw, c.O.ker⟩ : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)),
    KerFam (w.D Z) Gt cmp tw c.O.Gy) = ⟨col.Gt, col.cmp, w.tw Z, ker0⟩
  ker : KerT col.toColT c.O.X c.O.Gy ker0
  div : DivT n c.O.X
  th : ThT n c.O.th
  obj : ObjT c.O what₂
  ox : 𝒮.Ox K B f T w Z c.Wt c.O what₂

def BuiltC (𝒮 : Slots) : CP := fun K _ _ _ w Z c => Nonempty (Built 𝒮 K w Z c)

def IsBuilt (𝒮 : Slots) : V4.Slot := positionOf (BuiltC 𝒮)

def Has2 (𝒮 : Slots) : WP := HasZ fun K _ _ _ w Z => Nonempty (Lv2 𝒮 K w Z)

def Has3 (𝒮 : Slots) : WP := HasZ fun K _ _ _ w Z => Nonempty (Lv3 𝒮 K w Z)

def Has4 (𝒮 : Slots) : WP := HasZ fun K _ _ _ w Z => Nonempty (Lv4 𝒮 K w Z)

def pinAnd (p : WP) : WP := fun K B f T w => Pinned K B f T w ∧ p K B f T w

def AmbEx (𝒮 : Slots) : Prop := StepW Pinned fun K _ _ _ w => ∀ (Z : w.Lt) (l : Lv4 𝒮 K w Z), ∃ a a0, AmbAre l.what₂.r.Z a a0

def DivEx (𝒮 : Slots) : Prop := StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (l : Lv4 𝒮 K w Z), ∃ Y : DivX (w.D Z),
  Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧ (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧
    ∀ (O : Obj2 (w.D Z)) (t : RowsT K w Z l.Wt O.p0), O.X = Y → O.p0 = l.p0 → HEq t l.what₂ → Nonempty (𝒮.Ox K B f T w Z l.Wt O t)

def ThEx (𝒮 : Slots) : Prop := StepW Pinned fun K _ _ _ w => ∀ (Z : w.Lt) (l : Lv4 𝒮 K w Z), ∃ th : ThetaX (w.D Z), Nonempty (ThT l.n th)

theorem stepW_built {𝒮 : Slots} (h2 : StepW Start (Has2 𝒮)) (h3 : StepW (pinAnd (Has2 𝒮)) (Has3 𝒮))
    (h4 : StepW (pinAnd (Has3 𝒮)) (Has4 𝒮)) (h5 : StepW (pinAnd (Has4 𝒮)) (HasC (BuiltC 𝒮))) :
    StepW Start (HasC (BuiltC 𝒮)) :=
  have p : StepW Start Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h.1
  (p.and ((p.and ((p.and h2).trans h3)).trans h4)).trans h5

theorem supp_of_untw (w : ColW B f T) (h : T = TwDat.untw B T.pl) : Supp K B f T w := Or.inl h

theorem coh_of_untw (h : T = TwDat.untw B T.pl) : Coh B T := by
  rw [h]
  exact ⟨fun _ _ _ => ⟨rfl, rfl, rfl⟩, fun v => ⟨1, by change IsPrimitiveRoot _ (_ ^ 0); rw [pow_zero]; exact IsPrimitiveRoot.one⟩⟩

end GlobalTheory.Mem.Top.Bl

end
