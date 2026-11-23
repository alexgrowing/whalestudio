import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.MirabolicInclusion
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.Obj

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.IndefR.Links Formalism.IndefR.Arith

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure SlopeArithmeticParameters (R : RealDat D A Ks) where

  rd : ℝ

  χ : DirichletCharacter ℂ D.host.d

  Z : ℝ

  logOmK : ℝ

  logOm : ℝ

  Rw : ℝ

  PPp : ℝ

  PPpp : ℝ

  PP : ℝ

  PPT : ℝ

  Zpg : ℝ

  w : Fin D.R.m → D.what₂.Tau → ℝ

  w0 : Fin D.R.m → D.what₂.Tau → ℝ

  c1 : Fin D.R.m → D.what₂.Tau → ℝ

  ua : Fin D.R.m → D.what₂.Tau → ℝ

  kap : Fin D.R.m → ℝ

  ι : Fin D.R.m → Type
  fι : ∀ j, Fintype (ι j)
  nι : ∀ j, Nonempty (ι j)

  DY : Fin D.R.m → ℝ

  Ahs : Fin D.R.m → ℝ

  cs : Fin D.R.m → ℝ

  X : Fin D.R.m → ℝ

  cc : Fin D.R.m → ℝ

  E0 : Fin D.R.m → ℝ

  Qcc : Fin D.R.m → ℝ

  ρ : Fin D.R.m → ℝ

  R1 : Fin D.R.m → ℝ

  R2 : Fin D.R.m → ℝ

  Bn : Fin D.R.m → ℝ

  δ' : Fin D.R.m → ℝ

  h : ∀ j, ι j → ℝ

  sl : ∀ j, ι j → ℝ

  δc : ∀ j, ι j → ℝ

  dc : ∀ j, ι j → ℝ

  degc : ∀ j, ι j → ℝ

  PPf : Fin D.R.m → ℝ

  mv : Fin D.R.m → ℝ

  muU : Fin D.R.m → ℝ

  nA : Fin D.R.m → ℕ
  nB : Fin D.R.m → ℕ

  XA : ∀ j, InfinitePlace D.what₂.LL → Matrix (Fin (nA j)) (Fin (nA j)) ℂ
  XB : ∀ j, InfinitePlace D.what₂.LL → Matrix (Fin (nB j)) (Fin (nB j)) ℂ

  XN : ∀ j, InfinitePlace D.what₂.LL → Matrix (Fin (R.nW j)) (Fin (R.nW j)) ℂ

  LA : ∀ j, Submodule (𝓞 D.what₂.LL) (Fin (nA j) → D.what₂.LL)
  LB : ∀ j, Submodule (𝓞 D.what₂.LL) (Fin (nB j) → D.what₂.LL)

  NN : ∀ j, Submodule (𝓞 D.what₂.LL) (Fin (R.nW j) → D.what₂.LL)

  Ph : ∀ j, (Fin (nA j) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (nB j) → D.what₂.LL)

  PPh : Fin D.R.m → ℝ
  abelian₂ : Fin D.R.m → ℝ
  δ : Fin D.R.m → ℝ
  o' : Fin D.R.m → ℝ
  n2 : Fin D.R.m → ℝ

  volW : Fin D.R.m → ℝ

attribute [instance] SlopeArithmeticParameters.fι SlopeArithmeticParameters.nι

def SlopeArithmeticParameters.withNum {R : RealDat D A Ks} (J : SlopeArithmeticParameters R) (N : NumDatum) (hd : N.d = D.host.d) : SlopeArithmeticParameters R :=
  { J with rd := N.rd, χ := hd ▸ N.chiK, logOm := N.logOm }

def slopeParametersAtScale {R : RealDat D A Ks} (x : ℝ) (I : OnIn R) (J : SlopeArithmeticParameters R) (hd : NeZero D.host.d) : SlopeBoundParameters where
  Pl := D.what₂.Tau
  fPl := inferInstance
  x := x
  eps := I.eps
  rd := J.rd
  v := J.rd / 2
  dN := D.host.d
  dimNeZero := hd
  χ := J.χ
  Z := J.Z
  logOmK := J.logOmK
  logOm := J.logOm
  f := D.R.f
  m := D.R.m
  k := D.R.k
  S := I.Sc
  η := I.eta
  R := J.Rw
  PPp := J.PPp
  PPpp := J.PPpp
  PP := J.PP
  PPT := J.PPT
  Zpg := J.Zpg
  nV := D.R.nV
  Nr := D.R.r
  g12 := ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)

def slopeParameters (R : RealDat D A Ks) (F : Face D A) (I : OnIn R) (J : SlopeArithmeticParameters R) (hd : NeZero D.host.d) : SlopeBoundParameters :=
  slopeParametersAtScale (xAt F R) I J hd

def liftSlopeDataAtScale (R : RealDat D A Ks) (x : ℝ) (I : OnIn R) (J : SlopeArithmeticParameters R) (hd : NeZero D.host.d) (i : Fin D.R.m) :
    SlopeBoundLiftData D.what₂.LL (slopeParametersAtScale x I J hd) where
  w := J.w i
  w0 := J.w0 i
  c1 := J.c1 i
  ua := J.ua i
  kap := J.kap i
  q' := D.R.m - ((i : ℕ) + 1)
  pq := (D.R.k : ℝ) + D.R.m - 1 - 2 * ((D.R.m - ((i : ℕ) + 1) : ℕ) : ℝ)
  ι := J.ι i
  fι := inferInstance
  nι := inferInstance
  DY := J.DY i
  A := J.Ahs i
  cs := J.cs i
  X := J.X i
  cc := J.cc i
  E0 := J.E0 i
  Qcc := J.Qcc i
  ρ := J.ρ i
  R1 := J.R1 i
  R2 := J.R2 i
  Bn := J.Bn i
  δ' := J.δ' i
  h := J.h i
  sl := J.sl i
  δc := J.δc i
  dc := J.dc i
  degc := J.degc i
  PPf := J.PPf i
  mv := J.mv i
  muU := J.muU i
  nA := J.nA i
  nB := J.nB i
  nN := R.nW i
  XA := J.XA i
  XB := J.XB i
  XN := J.XN i
  LA := J.LA i
  LB := J.LB i
  NN := J.NN i
  Mk := MsOf R i
  φ := J.Ph i
  e := eOn R i
  g := Fintype.card G
  PPh := J.PPh i
  abelian₂ := J.abelian₂ i
  δ := J.δ i
  o' := J.o' i
  n2 := 0

def liftSlopeData (R : RealDat D A Ks) (F : Face D A) (I : OnIn R) (J : SlopeArithmeticParameters R) (hd : NeZero D.host.d) (i : Fin D.R.m) :
    SlopeBoundLiftData D.what₂.LL (slopeParameters R F I J hd) :=
  liftSlopeDataAtScale R (xAt F R) I J hd i

def volumeScaledLatticeFrames {R : RealDat D A Ks} {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df) (eJ : Bs.J ≃ Fin D.R.m)
    (J : SlopeArithmeticParameters R) (i : Bs.J) : InfinitePlace D.what₂.LL → Matrix (Fin (S.dW i)) (Fin (S.dW i)) ℂ :=
  fun v => ((Real.sqrt (J.volW (eJ i)) : ℝ) : ℂ) • S.XW i v

def latticeFramesAtBaseLevel (R : RealDat D A Ks) (F : Face D A) (J : SlopeArithmeticParameters R) (i : Fin D.R.m) :
    InfinitePlace D.what₂.LL → Matrix (Fin ((Sb R F).dW i)) (Fin ((Sb R F).dW i)) ℂ :=
  volumeScaledLatticeFrames (Sb R F) (Equiv.refl _) J i

section Joint

variable (R : RealDat D A Ks) (F : Face D A) (I : OnIn R) (J : SlopeArithmeticParameters R) (hd : NeZero D.host.d)

structure SlopeBoundConditions (Ca Cb Cf Cc C1 Cm Cn : ℝ) : Prop where
  kl : LeafKL (slopeParameters R F I J hd)
  cn : LeafCN (slopeParameters R F I J hd)
  fe : LeafFE (slopeParameters R F I J hd)
  diff : LeafDiff (slopeParameters R F I J hd)
  norm : LeafNorm (slopeParameters R F I J hd)
  page : PageParams (slopeParameters R F I J hd)
  fac : ∀ j, FacParams Cf (liftSlopeData R F I J hd j)
  degFlat : ∀ j, LeafDegFlat Cc (liftSlopeData R F I J hd j)
  exportL : ∀ j, LeafExport Cf (liftSlopeData R F I J hd j)
  cut : ∀ j, LeafCut (liftSlopeData R F I J hd j)
  shareBad : ∀ j, LeafShareBad (liftSlopeData R F I J hd j)
  badRows : ∀ j, LeafBadRows (liftSlopeData R F I J hd j)
  muN : ∀ j, LeafMuN (liftSlopeData R F I J hd j)
  lam : ∀ j, LeafLam (liftSlopeData R F I J hd j)
  record : ∀ j, LeafRecord (latticeFramesAtBaseLevel R F J j) ((Sb R F).M j) (liftSlopeData R F I J hd j)
  note2 : ∀ j, LeafNote2 Cn (liftSlopeData R F I J hd j)
  measure : ∀ j, LeafMeasure Cm (D := (Sb R F).D) ((Sb R F).XW j) (latticeFramesAtBaseLevel R F J j) ((Sb R F).M j) (slopeParameters R F I J hd)
  def0 : ∀ j, (liftSlopeData R F I J hd j).q' = 0 → LeafDef C1 Cf (liftSlopeData R F I J hd j)
  root : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafRoot (liftSlopeData R F I J hd j)
  flat : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafFlat Cf (liftSlopeData R F I J hd j)
  deg : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafDeg (liftSlopeData R F I J hd j)
  rho : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafRho (liftSlopeData R F I J hd j)
  share : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafShare (liftSlopeData R F I J hd j)
  small : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafSmall (liftSlopeData R F I J hd j)
  means : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafMeans Ca Cb (liftSlopeData R F I J hd j)
  hs : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafHS (liftSlopeData R F I J hd j)
  sum : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafSum (liftSlopeData R F I J hd j)
  i13 : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → CrudeSizeBound (liftSlopeData R F I J hd j)
  eps : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafEps (liftSlopeData R F I J hd j)
  descent : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafDescent (liftSlopeData R F I J hd j)
  ph : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafPh (liftSlopeData R F I J hd j)
  gmin : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → LeafGmin (liftSlopeData R F I J hd j)
  compParams : ∀ j, (liftSlopeData R F I J hd j).q' ≠ 0 → CompParams Ca Cb (liftSlopeData R F I J hd j)

theorem covol_of_leaves (Ca Cb Cf Cc C1 Cm Cn : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc)
    (hC1 : 0 ≤ C1) (hCm : 0 ≤ Cm) (C CH : ℝ) (hC : C = slopeBoundConstant Ca Cb Cf Cc C1 Cm)
    (hL : SlopeBoundConditions R F I J hd Ca Cb Cf Cc C1 Cm Cn) (hD : 0 < (Sb R F).D) (hdW : ∀ j, (Sb R F).dW j = (Sb R F).D)
    (hF : (Sb R F).Frames) (hT : ScaleTies (F.fc (R.toCx F).zs).Z (slopeParameters R F I J hd) (liftSlopeData R F I J hd)) :
    R.LCovol F C CH := by
  subst hC
  exact slope_bound_of_conditions Ca Cb Cf Cc C1 Cm Cn hCa hCb hCf hCc hC1 hCm (Sb R F) (F.fc (R.toCx F).zs).Z CH
    (slopeParameters R F I J hd) (liftSlopeData R F I J hd) (latticeFramesAtBaseLevel R F J) hL.kl hL.cn hL.fe hL.diff hL.norm hL.page hL.fac hL.degFlat
    hL.exportL hL.cut hL.shareBad hL.badRows hL.muN hL.lam hL.record hL.note2 hL.measure hL.def0 hL.root hL.flat hL.deg
    hL.rho hL.share hL.small hL.means hL.hs hL.sum hL.i13 hL.eps hL.descent hL.ph hL.gmin hL.compParams hD hdW hF hT

theorem scaleTies_of (hb : (F.fc (R.toCx F).zs).Z.b = (slopeParameters R F I J hd).b)
    (hmain : ∀ j, (F.fc (R.toCx F).zs).Z.l3m j = (liftSlopeData R F I J hd j).main)
    (hunit : (F.fc (R.toCx F).zs).Z.l3u = (slopeParameters R F I J hd).B0 * (slopeParameters R F I J hd).llx) :
    ScaleTies (F.fc (R.toCx F).zs).Z (slopeParameters R F I J hd) (liftSlopeData R F I J hd) := by
  refine ⟨rfl, hb, ?_, hmain, hunit, ?_, fun j => ⟨?_, rfl⟩⟩
  · show (Fintype.card (Fin D.R.m) : ℝ) = (D.R.m : ℝ)
    rw [Fintype.card_fin]
  · intro a b h
    have h' : D.R.m - ((a : ℕ) + 1) = D.R.m - ((b : ℕ) + 1) := h
    have ha := a.2
    have hb := b.2
    exact Fin.ext (by omega)
  · show ((D.R.m - ((j : ℕ) + 1) : ℕ) : ℝ) + 1 ≤ (D.R.m : ℝ)
    have hj := j.2
    rw [← Nat.cast_add_one, Nat.cast_le]
    omega

end Joint

end Formalism.IndefR.Obj
