import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.LocalToGlobal.GlobalTheory.FamRec
import Formalism.SizeWindowBrackets.TranslateWordBoundHypotheses
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamCol

open Formalism Formalism.BasicNotions Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.DIV

structure PlDat (K : Type) (I : Type) where
  N : NumDatum
  Cs : Arith.Cst
  Lv : Arith.Lev N
  sd : K
  code : I → Code N

structure RowArg {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} (C : ColObj K I) where
  Wd : Type
  [indexWFirst : AddCommGroup Wd]
  [indexWSecond : Module K Wd]
  [indexWThird : Module (𝓞 K) Wd]
  [indexWFourth : IsScalarTower (𝓞 K) K Wd]
  κ : Type
  [firstRealIndex : Fintype κ]
  [secondRealIndex : DecidableEq κ]
  κ₁ : Type
  [firstRationalIndex : Fintype κ₁]
  [secondRationalIndex : DecidableEq κ₁]
  b' : Basis κ K Wd
  X' : InfinitePlace K → Matrix κ κ ℂ
  cc : Submodule (𝓞 K) Wd
  B : ∀ u, (C.M u).V →ₗ[K] Wd
  v : InfinitePlace K
  Y : ∀ u, Matrix (C.M u).ι (C.M u).ι ℂ
  Y' : Matrix κ κ ℂ
  Ball : ∀ u, Matrix (κ ⊕ κ₁) (C.M u).ι ℂ
  γ : I → ℝ
  Bf : ∀ u, Matrix (κ ⊕ κ₁) (C.Mf u).ι ℂ
  h : I → ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ

attribute [instance] RowArg.indexWFirst RowArg.indexWSecond RowArg.indexWThird RowArg.indexWFourth RowArg.firstRealIndex RowArg.secondRealIndex RowArg.firstRationalIndex RowArg.secondRationalIndex

section Fam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

def famC [IsTotallyComplex K] (m : ℕ) (C : ColObj K I) (P : PlDat K I) (R : RowArg C) : LChain2.Fam I m where
  K := K
  Wd := R.Wd
  κ := R.κ
  κ₁ := R.κ₁
  V := fun u => (C.M u).V
  ι := fun u => (C.M u).ι
  Vf := fun u => (C.Mf u).V
  ιf := fun u => (C.Mf u).ι
  b' := R.b'
  X' := R.X'
  cc := R.cc
  b := fun u => (C.M u).b
  X := fun u => (C.M u).X
  M := fun u => (C.M u).L
  N0 := C.Nu
  bf := fun u => (C.Mf u).b
  Xf := fun u => (C.Mf u).X
  Mf := fun u => (C.Mf u).L
  σ := C.sgExp
  τ := C.tauExp
  B := R.B
  v := R.v
  Y := R.Y
  Y' := R.Y'
  Ball := R.Ball
  γ := R.γ
  Bf := R.Bf
  Vr := fun u => C.Vr u R.v
  S := C.S
  gain := fun j w => Arith.gainD P.N P.Cs P.Lv (Arith.pOf (Arith.hs w)) (j.1 + 1)
  Fj := fun j w => P.N.FjP (j.1 + 1) (Arith.pOf (Arith.hs w))
  Ej := fun u j w => Arith.E P.N P.Cs P.Lv P.sd (P.code u) (j.1 + 1) (Arith.hs w)
  iop := Arith.io P.N P.Cs
  T := C.T
  h := R.h
  lam := C.lamT
  Dstar := C.Dstar
  η0 := R.η0
  η1 := R.η1
  e0 := R.e0

theorem famC_closed [IsTotallyComplex K] (C : ColObj K I) (P : PlDat K I) (R : RowArg C) :
    (famC P.N.R.m C P R).gain = Arith.famGain P.N P.Cs P.Lv ∧ (famC P.N.R.m C P R).Fj = Arith.famF P.N ∧
    (∀ u, (famC P.N.R.m C P R).Ej u = Arith.famE P.N P.Cs P.Lv P.sd (P.code u)) ∧
    (∀ m u, (famC m C P R).N' u = C.Npr u) ∧ (∀ m u, (famC m C P R).ItM u = C.ItM u) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def ColFacts (C : ColObj K I) : Prop := ∃ J : ColIface K I, J.toColObj = C

structure PlaceDataCompatible (C : ColObj K I) (P : PlDat K I) : Prop where
  f : C.f = P.N.R.f
  k : C.k = P.N.R.k
  m : C.m = P.N.R.m
  sd : Arith.SdOk P.N P.sd
  code : ∀ u, P.code u ∈ P.Lv.Ws
  T : ∀ u, C.T u = P.Lv.T (P.code u)
  overPi : ∀ u w, prW w = C.T u → (C.overPi u w ↔ 0 < vAdd w (Arith.elt P.sd (P.Lv.piT (P.code u))))
  supp : C.supp = Arith.supp P.N P.Lv K
  tau : C.tau = fun w => Arith.tau P.N P.Cs (Arith.pOf w)
  sg : ∀ u, C.sg u = Arith.sg P.N P.Cs P.Lv P.sd (P.code u)

structure Service (C : ColObj K I) (P : PlDat K I) : Prop where
  len : ∀ u, ∀ w ∈ C.supp, prW w ≠ C.T u →
    ((C.lenMN u w : ℚ) : ℝ) ≤ (C.dM u : ℝ) * (Arith.tau P.N P.Cs (Arith.pOf w) + Arith.io P.N P.Cs (Arith.pOf w))

structure DatWin (P : PlDat K I) : Prop where
  d_le : (P.N.d : ℝ) ≤ P.N.sc.X'' P.N.R.n
  dgam : ∀ p : ℕ, p.Prime → p ∣ P.Lv.DGam → (p : ℝ) ≤ P.N.sc.X'' P.N.R.n

structure PlSizes (C : ColObj K I) (P : PlDat K I) (bb : ℝ) : Prop where
  Ta : ∑ w ∈ C.supp, Arith.sz w (Arith.tau P.N P.Cs (Arith.pOf w)) ≤ bb ^ 2
  level : ∀ u, 4 * (C.f : ℝ) / (C.T u : ℝ) * bb ^ 2
    + (C.f : ℝ) * Real.log ((C.T u : ℝ) - 1) / ((C.T u : ℝ) - 2) ≤ 1

def rdPr (P : PlDat K I) (u : I) : Finset ℕ :=
  P.N.suppP ∪ P.Lv.DGam.primeFactors ∪ {P.Lv.T (P.code u)}

structure RowHyp [Fintype I] (C : ColObj K I) (R : RowArg C) (sg : ℝ) : Prop where
  X' : ∀ w, IsUnit (R.X' w).det
  Y : ∀ u, IsUnit (R.Y u).det
  Y' : IsUnit R.Y'.det
  cc_fg : R.cc.FG
  cc_span : Submodule.span K (R.cc : Set R.Wd) = ⊤
  what₂ : 0 < Fintype.card R.κ
  into : ∀ u, (C.Npr u).map ((R.B u).restrictScalars (𝓞 K)) ≤ R.cc
  ht : ∀ u, R.B u ≠ 0 → htMap (C.M u).b (C.M u).X R.b' R.X' (R.B u) ≤ R.h u
  block : ∀ u (k : R.κ) (j : (C.M u).ι), R.Ball u (Sum.inl k) j =
    (R.Y'⁻¹ * (LinearMap.toMatrix (C.M u).b R.b' (R.B u)).map R.v.embedding * R.Y u) k j
  γ : ∀ u, 0 < R.γ u
  Ball : ∀ u, R.Ball u = R.Bf u * C.Vr u R.v
  sg_pos : 0 < sg
  sg_le : sg ≤ 1 / 20
  proviso : C.Dstar / sg ≤ ∑ u, (Fintype.card (C.Mf u).ι : ℝ)
  η0_ge : -1 ≤ R.η0
  η0_le : R.η0 ≤ sg / 2
  η1_le : R.η1 ≤ sg / 2
  exponent_bound_ter : 0 ≤ R.e0
  sqrt_error_le_half : Real.sqrt R.e0 ≤ sg / 2
  inputS : MatrixLatticeEstimates.InputSG R.Bf R.γ C.Dstar R.η0 R.η1 R.e0

end Fam

def ClosedSums : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) (m : ℕ) (C : ColObj K I)
    (P : PlDat K I) (R : RowArg C), P.N.R.m = m → PlaceDataCompatible C P →
    (famC m C P R).Ga = Arith.Ga P.N P.Cs P.Lv K ∧
    (famC m C P R).Fo = Arith.Fo P.N P.Lv K ∧
    (∀ u (j : Fin m), (famC m C P R).EeJ u j =
      ∑ w ∈ Arith.supp P.N P.Lv K, Arith.sz w (Arith.E P.N P.Cs P.Lv P.sd (P.code u) (j.1 + 1) w)) ∧
    (∀ u, ∑ j : Fin m, (famC m C P R).EeJ u j = Arith.Ee P.N P.Cs P.Lv P.sd (P.code u)) ∧
    (famC m C P R).Ta = ∑ w ∈ Arith.supp P.N P.Lv K, Arith.sz w (Arith.tau P.N P.Cs (Arith.pOf w)) ∧
    (famC m C P R).IO = Arith.IOsum P.N P.Cs P.Lv K

def PlaceFactsConcrete : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) (m : ℕ) (C : ColObj K I)
    (P : PlDat K I) (R : RowArg C), P.N.R.m = m → ColFacts C → PlaceDataCompatible C P → P.Cs.admitted → Service C P → DatWin P →
    LChain6.Fam6.PlaceIn' (famC m C P R) C.f (P.N.g 0) (P.N.g 1) (P.N.sc.X'' P.N.R.n)

def LatticeHypothesisOfColumnFacts : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) [Fintype I] [Nonempty I] (m : ℕ)
    (C : ColObj K I) (P : PlDat K I) (R : RowArg C) (sg : ℝ), ColFacts C → RowHyp C R sg → (famC m C P R).LatHyp sg

def PlaceHypothesisOfPlaceSizes : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) (m : ℕ) (C : ColObj K I)
    (P : PlDat K I) (R : RowArg C) (bb : ℝ), P.N.R.m = m → ColFacts C → PlaceDataCompatible C P → P.Cs.admitted →
    Service C P → PlSizes C P bb → (famC m C P R).PlaceHyp C.f bb

def RoundingLossBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) (m : ℕ) (C : ColObj K I)
    (P : PlDat K I) (R : RowArg C), P.N.R.m = m → PlaceDataCompatible C P →
    (∀ δ ∈ P.Lv.Ws, P.N.sc.X'' P.N.R.n < (P.Lv.T δ : ℝ)) →
    ∀ u, (famC m C P R).Rd u ≤ 2 * ∑ p ∈ rdPr P u, Real.log (p : ℝ)

structure Pt (I : Type) where
  K : Type
  [i1 : Field K]
  [i2 : NumberField K]
  [i3 : StarRing K]
  [i4 : IsTotallyComplex K]
  C : ColObj K I
  P : PlDat K I
  R : RowArg C

attribute [instance] Pt.i1 Pt.i2 Pt.i3 Pt.i4

def Pt.fam {I : Type} (m : ℕ) (Q : Pt I) : LChain2.Fam I m := famC m Q.C Q.P Q.R

structure Pt.OkIn {I : Type} (Q : Pt I) (m f g₁ g₂ : ℕ) (Xpp : ℝ) : Prop where
  m : Q.P.N.R.m = m
  f : Q.C.f = f
  g0 : Q.P.N.g 0 = g₁
  g1 : Q.P.N.g 1 = g₂
  Xpp : Q.P.N.sc.X'' Q.P.N.R.n = Xpp
  facts : ColFacts Q.C
  tied : PlaceDataCompatible Q.C Q.P
  cst : Q.P.Cs.admitted
  service : Service Q.C Q.P
  win : DatWin Q.P

structure Pt.Ok {I : Type} (Q : Pt I) (m f : ℕ) (bb : ℝ) : Prop where
  m : Q.P.N.R.m = m
  f : Q.C.f = f
  facts : ColFacts Q.C
  tied : PlaceDataCompatible Q.C Q.P
  cst : Q.P.Cs.admitted
  service : Service Q.C Q.P
  sizes : PlSizes Q.C Q.P bb
  above : ∀ δ ∈ Q.P.Lv.Ws, Q.P.N.sc.X'' Q.P.N.R.n < (Q.P.Lv.T δ : ℝ)

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

def famQ (m : ℕ) (Q : ∀ u0, Pt (W u0)) : ∀ u0, Fam (W u0) m := fun u0 => (Q u0).fam m

abbrev dataQ (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0)) :
    Data H W TT m (PhiSet (H := H)).card :=
  mkData G cHH D ell N TT T2 a w (famQ m Q)

def objQ {TT : Finset H} (O : LChain6.SizeCountLevelObjects H W m TT) (Q : ∀ u0 : H, Pt (W u0)) : LChain6.SizeCountLevelObjects H W m TT :=
  { O with X := fun u0 u => (Q u0).C.Xu u, dst := fun u0 u => (Q u0).C.dstar u }

def RemainingInputsAfter (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0))
    (Rw : ∀ u0, LChain6.Rows (famQ m Q u0)) (O : LChain6.SizeCountLevelObjects H W m TT)
    (η θ eK K logOm C0 cZ cL cE5 c5 : ℝ) (g₁ g₂ : ℕ) : Prop :=
  (∀ u0, RowHyp (Q u0).C (Q u0).R (sgX G C.cHH)) ∧
  (∀ u0, (famQ m Q u0).Ta ≤ bTx G.x G.ε ^ 2) ∧
  28 ≤ C.cSl1 ∧ G.eBar ≤ 1 / 4 ∧
  LChain6.DivIn G C TT T2 a (famQ m Q) Rw logOm C0 g₁ g₂ ∧
  ((∀ u0 (u : W u0),
      SectionsFourToSixTransfer.ZiiR (dataQ G C.cHH D ell N TT T2 a w Q) cZ O.Sc O.LZ (Real.log ((Q u0).C.T u : ℝ)) ≤ (Q u0).C.zLow u ∧
      (Q u0).C.zUp u ≤ SectionsFourToSixTransfer.ZiiiR (dataQ G C.cHH D ell N TT T2 a w Q) cZ O.Sc O.LZ (Real.log ((Q u0).C.T u : ℝ))) ∧
    SectionsFourToSixTransfer.ZWindows (dataQ G C.cHH D ell N TT T2 a w Q) cZ cL (c5 + 1) O.Sc O.LZ ∧
    SectionsFourToSixTransfer.cSlopeZ cZ cL (c5 + 1) ≤ C.cSlope) ∧
  ((∀ u0,
      SectionsFourToSixTransfer.exactMain (dataQ G C.cHH D ell N TT T2 a w Q) O.bN u0 - cE5 * Real.log (bTx G.x G.ε) - 1 ≤ (Q u0).C.xLow ∧
      (Q u0).C.xUp ≤ c5 * (m : ℝ) * Real.log (bTx G.x G.ε) ∧ (Q u0).C.xVar ≤ c5 * Real.log G.k) ∧
    SectionsFourToSixTransfer.LevelWindow (dataQ G C.cHH D ell N TT T2 a w Q) O.Gam (fun u0 u => (Q u0).C.Xu u) ∧
    SectionsFourToSixTransfer.ExactWindows (dataQ G C.cHH D ell N TT T2 a w Q) O.bN ∧
    SectionsFourToSixTransfer.CountWindows (LChain6.withGam (dataQ G C.cHH D ell N TT T2 a w Q) O.Gam) c5 O.Gam ∧
    cE5 + 6 ≤ c5 ∧ c5 + 3 ≤ C.cCount) ∧
  (SectionsFourToSixTransfer.IndexWindows (dataQ G C.cHH D ell N TT T2 a w Q) O.aM O.Wt O.bt ∧
    ∀ u0 u, (Q u0).C.lamT u ≤ SectionsFourToSixTransfer.lambdaIndex (dataQ G C.cHH D ell N TT T2 a w Q) O.aM (O.VV u0 u) O.Wt O.bt) ∧
  LChain6.LevelWin (dataQ G C.cHH D ell N TT T2 a w Q) c5 ∧
  (Real.log g₁ ≤ XppH H G ∧ Real.log g₂ ≤ XppH H G ∧ (c5 + 1) * (m : ℝ) * Real.log (bTx G.x G.ε) ≤ XppH H G) ∧
  (∀ u0, (famQ m Q u0).del ≤ G.delBar ∧ 5 * sgX G C.cHH + 3 * Real.sqrt (famQ m Q u0).deF ≤ G.etaBar ∧
    2 * (Q u0).R.e0 ≤ G.eBar) ∧
  ErrWindows (dataQ G C.cHH D ell N TT T2 a w Q) C (XppH H G) eK K ∧
  GrowthInequalitySizes TT T2 a w N G.x (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ ∧
  CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
  RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε)

def FirstLayerInputsAfter : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0))
    (Rw : ∀ u0, LChain6.Rows (famQ m Q u0)) (O : LChain6.SizeCountLevelObjects H W m TT)
    (η θ eK K logOm C0 cZ cL cE5 c5 : ℝ) (g₁ g₂ : ℕ), (∀ u0, Nonempty (W u0)) →
    (∀ u0, (Q u0).OkIn m (PhiSet (H := H)).card g₁ g₂ (XppH H G)) →
    RemainingInputsAfter D ell G C N TT T2 a w Q Rw O η θ eK K logOm C0 cZ cL cE5 c5 g₁ g₂ →
    LChain6.Inputs6b D ell G C N TT T2 a w (famQ m Q) Rw (objQ O Q) η θ eK K logOm C0 cZ cL cE5 c5 g₁ g₂

def FirstLayerInputsBefore : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0))
    (Rw : ∀ u0, LChain6.Rows (famQ m Q u0)) (O : LChain6.SizeCountLevelObjects H W m TT)
    (η θ eK K logOm C0 cZ cL cE5 c5 : ℝ) (g₁ g₂ : ℕ), (∀ u0, Nonempty (W u0)) →
    (∀ u0, (Q u0).OkIn m (PhiSet (H := H)).card g₁ g₂ (XppH H G)) →
    RemainingInputsAfter D ell G C N TT T2 a w Q Rw O η θ eK K logOm C0 cZ cL cE5 c5 g₁ g₂ →
    LChain6.Inputs6a D ell G C 7 N TT T2 a w (famQ m Q) Rw η θ eK K logOm C0 g₁ g₂

def ThresholdTotalBound : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {W : Ω → H → Type} [∀ o u0, Fintype (W o u0)] (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ)
    (TT : Finset H) (a : Ω → H → ℝ) (w : Ω → H → Fin m → E0 × H → ℝ) (Q : ∀ o u0, Pt (W o u0)) (Lp : H → Ω → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → Ω → ℝ) (Cord eW KW : ℝ),
    LossHyp D G C N TT a w (fun o u0 => (Q o u0).fam m) Lp P π s sB BAD Sig Cord eW KW → PrimeWindowSizeBounds.LargeX G.x G.ε eW KW →
    ∀ (o : Ω) (u0 : H), LChain6.Fam6.GainIn ((Q o u0).fam m) (inertPs D N) (Lp u0 o).cl (TT.card : ℝ) (aTx G.x G.ε) →
    (m : ℝ) ≤ G.x → (TT.card : ℝ) ≤ P.n → ((Q o u0).fam m).Ta ≤ bTx G.x G.ε ^ 2

def OkQ (G : Glob) (m : ℕ) (Q : ∀ u0 : H, Pt (W u0)) : Prop :=
  ∀ u0, (Q u0).Ok m (PhiSet (H := H)).card (bTx G.x G.ε)

def SlWin (G : Glob) (C : Consts) (cT : ℝ) (TT : Finset H) (m : ℕ) (Q : ∀ u0 : H, Pt (W u0)) : Prop :=
  ∀ u0 (u : W u0),
    (Q u0).C.lamT u ≤ cT * (TT.card : ℝ) * (m : ℝ) * (aTx G.x G.ε / G.k + bpTx G.x G.ε) ∧
    2 * ∑ p ∈ rdPr (Q u0).P u, Real.log (p : ℝ) ≤ C.cSl1 * XppH H G

def PlaceSizesOfSlopeWindow : Prop :=
  ∀ (G : Glob) (C : Consts) (cT : ℝ) (TT : Finset H) (Q : ∀ u0 : H, Pt (W u0)), 4 ≤ C.cSl1 → 4 * cT ≤ C.cSl1 →
    OkQ G m Q → SlWin G C cT TT m Q → SizesPl G C cT TT (famQ m Q)

def SlopeLemmaConcrete : Prop :=
  ∀ (G : Glob) (C : Consts) (cT : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0)), (∀ u0, Nonempty (W u0)) → 0 < G.x → 0 < G.k →
    4 ≤ C.cSl1 → 4 * cT ≤ C.cSl1 → OkQ G m Q → SlWin G C cT TT m Q →
    QuotientSlopeBoundsWith (dataQ G C.cHH D ell N TT T2 a w Q) C (XppH H G)

def ColumnLatticeSlopes : Prop :=
  ∀ (G : Glob) (C : Consts) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0)) (cZ cL cU Sc LZ : ℝ),
    (∀ u0, ColFacts (Q u0).C) →
    SectionsFourToSixTransfer.ZWindows (dataQ G C.cHH D ell N TT T2 a w Q) cZ cL cU Sc LZ →
    SectionsFourToSixTransfer.LogTUp (dataQ G C.cHH D ell N TT T2 a w Q) cU →
    (∀ u0 (u : W u0),
      SectionsFourToSixTransfer.ZiiR (dataQ G C.cHH D ell N TT T2 a w Q) cZ Sc LZ (Real.log ((Q u0).C.T u : ℝ)) ≤ (Q u0).C.zLow u ∧
      (Q u0).C.zUp u ≤ SectionsFourToSixTransfer.ZiiiR (dataQ G C.cHH D ell N TT T2 a w Q) cZ Sc LZ (Real.log ((Q u0).C.T u : ℝ))) →
    SectionsFourToSixTransfer.cSlopeZ cZ cL cU ≤ C.cSlope → (dataQ G C.cHH D ell N TT T2 a w Q).Slopes C

def WindowCountBound : Prop :=
  ∀ (G : Glob) (C : Consts) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0)) (c5 Gam : ℝ),
    (∀ u0, ColFacts (Q u0).C) →
    SectionsFourToSixTransfer.CountWindows (LChain6.withGam (dataQ G C.cHH D ell N TT T2 a w Q) Gam) c5 Gam →
    (∀ u0,
      SectionsFourToSixTransfer.mainCount (dataQ G C.cHH D ell N TT T2 a w Q) u0
        - c5 * (Real.log (bTx G.x G.ε) + (m : ℝ) ^ 2 * Real.log (bTx G.x G.ε) / G.k) ≤ (Q u0).C.xLow ∧
      (Q u0).C.xUp ≤ c5 * (m : ℝ) * Real.log (bTx G.x G.ε) ∧ (Q u0).C.xVar ≤ c5 * Real.log G.k) →
    SectionsFourToSixTransfer.LevelWindow (dataQ G C.cHH D ell N TT T2 a w Q) Gam (fun u0 u => (Q u0).C.Xu u) →
    c5 + 3 ≤ C.cCount → Count5 (dataQ G C.cHH D ell N TT T2 a w Q) C

def RestInputs (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0)) (η θ eK K CL : ℝ) : Prop :=
  (∀ u0, RowHyp (Q u0).C (Q u0).R (sgX G C.cHH)) ∧
  0 < G.v ∧ G.eBar ≤ 1 / 4 ∧
  (dataQ G C.cHH D ell N TT T2 a w Q).DIV C ∧
  EComp5 (dataQ G C.cHH D ell N TT T2 a w Q) C ∧
  (dataQ G C.cHH D ell N TT T2 a w Q).HComp C ∧
  (∀ u0, (dataQ G C.cHH D ell N TT T2 a w Q).s u0 - muMinDef (Q u0).R.b' (Q u0).R.X' (Q u0).R.cc
    ≤ G.x ^ C.cHH * bTx G.x G.ε) ∧
  (∀ u0, (famQ m Q u0).del ≤ G.delBar ∧ 5 * sgX G C.cHH + 3 * Real.sqrt (famQ m Q u0).deF ≤ G.etaBar ∧
    2 * (Q u0).R.e0 ≤ G.eBar) ∧
  ErrWindows (dataQ G C.cHH D ell N TT T2 a w Q) C (XppH H G) eK K ∧
  GrowthInequalityRemainingHyps D ell N TT T2 a w G.x G.ε (bTx G.x G.ε) (bpTx G.x G.ε) η (XpTx G.x G.ε) θ CL ∧
  CostWindows G.x (fPl H) (bTx G.x G.ε) η θ ∧
  RestSize G.ε G.x (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε) ∧
  LossBounds (dataQ G C.cHH D ell N TT T2 a w Q) C

def FamilyHypothesesOfCountsAndSlopes : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0)) (η θ eK K CL : ℝ),
    (∀ u0, Nonempty (W u0)) → 4 ≤ C.cSl1 → 4 * cT ≤ C.cSl1 → OkQ G m Q → SlWin G C cT TT m Q →
    Count5 (dataQ G C.cHH D ell N TT T2 a w Q) C → (dataQ G C.cHH D ell N TT T2 a w Q).Slopes C →
    RestInputs D ell G C N TT T2 a w Q η θ eK K CL →
    Inputs2 D ell G C cT N TT T2 a w (famQ m Q) η θ eK K CL

def NodeChainStatement : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0)) (η θ eK K CL eD eL cHH : ℝ),
    (∀ u0, Nonempty (W u0)) → C.eDiv ≤ eD → C.eLoss ≤ eL → C.cHH ≤ cHH → HostFacts D →
    4 ≤ C.cSl1 → 4 * cT ≤ C.cSl1 → OkQ G m Q → SlWin G C cT TT m Q →
    Count5 (dataQ G C.cHH D ell N TT T2 a w Q) C → (dataQ G C.cHH D ell N TT T2 a w Q).Slopes C →
    RestInputs D ell G C N TT T2 a w Q η θ eK K CL →
    Chain2aCore eD eL K cHH eK CL G.ε G.x

structure SameNumbers {I : Type} [Fintype I] {m : ℕ} (F F' : Fam I m) : Prop where
  du : ∀ u, F.du u = F'.du u
  dM : ∀ u, F.dM u = F'.dM u
  T : ∀ u, F.T u = F'.T u
  muN : ∀ u, muDef (F.b u) (F.X u) (F.N' u) = muDef (F'.b u) (F'.X u) (F'.N' u)
  muMaxN : ∀ u, muMaxDef (F.b u) (F.X u) (F.N' u) = muMaxDef (F'.b u) (F'.X u) (F'.N' u)
  h : ∀ u, F.h u = F'.h u
  muM : ∀ u, muDef (F.bf u) (F.Xf u) (F.Mf u) = muDef (F'.bf u) (F'.Xf u) (F'.Mf u)
  muMaxM : ∀ u, muMaxDef (F.bf u) (F.Xf u) (F.Mf u) = muMaxDef (F'.bf u) (F'.Xf u) (F'.Mf u)
  EeJ : ∀ u j, F.EeJ u j = F'.EeJ u j
  muCC : muDef F.b' F.X' F.cc = muDef F'.b' F'.X' F'.cc
  muMinCC : muMinDef F.b' F.X' F.cc = muMinDef F'.b' F'.X' F'.cc
  Fo : F.Fo = F'.Fo
  Ga : F.Ga = F'.Ga
  Ta : F.Ta = F'.Ta
  IO : F.IO = F'.IO
  del : F.del = F'.del
  e0 : F.e0 = F'.e0

def DependsOnlyOnNumbers : Prop :=
  ∀ (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm Fm' : ∀ u0, Fam (W u0) m), (∀ u0, SameNumbers (Fm u0) (Fm' u0)) →
    FamRec.FieldEq (mkData G cHH D ell N TT T2 a w Fm) (mkData G cHH D ell N TT T2 a w Fm') (Equiv.refl _) (Equiv.refl _)

end Family

section Rec

structure RowJoint {D : D7} {C : ColObj D.what₂.LL D.what₂.Word} (R : RowArg C) : Prop where
  h : ∀ u, R.h u = D.div.h u
  muCC : muDef R.b' R.X' R.cc = D.div.RR.muDual
  muMinCC : muMinDef R.b' R.X' R.cc = D.div.RR.muMinDual
  del : 1 - (Fintype.card R.κ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) = D.what₂.delp

structure PlJoint {D : D7} (L : SizeData₂ D) (P : PlDat D.what₂.LL D.what₂.Word) : Prop where
  Ga : L.Ga = Arith.Ga P.N P.Cs P.Lv D.what₂.LL
  Fo : L.Fo = Arith.Fo P.N P.Lv D.what₂.LL
  E : ∀ u, ∀ j ∈ P.N.lifts, ∑ w ∈ L.supp, SizeData₂.sz w (L.E u j w) =
    ∑ w ∈ Arith.supp P.N P.Lv D.what₂.LL, Arith.sz w (Arith.E P.N P.Cs P.Lv P.sd (P.code u) j w)
  Ta : ∑ w ∈ L.supp, SizeData₂.sz w (L.tau w) =
    ∑ w ∈ Arith.supp P.N P.Lv D.what₂.LL, Arith.sz w (Arith.tau P.N P.Cs (Arith.pOf w))
  IO : ∑ w ∈ L.supp, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.io w = Arith.IOsum P.N P.Cs P.Lv D.what₂.LL

def RecordLocalAgreement : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (m : ℕ) (C : ColObj D.what₂.LL D.what₂.Word) (P : PlDat D.what₂.LL D.what₂.Word) (R : RowArg C),
    C.RecJoint D → P.N.R.m = m → PlaceDataCompatible C P → D.NuFull → RowJoint R → PlJoint L P →
    FamRec.LocalTie L m (famC m C P R)

def SameNumbersUnderJoint : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (m : ℕ) (A : FamRec.Mx D) (C : ColObj D.what₂.LL D.what₂.Word)
    (P : PlDat D.what₂.LL D.what₂.Word) (R : RowArg C),
    C.RecJoint D → P.N.R.m = m → PlaceDataCompatible C P → D.NuFull → RowJoint R → PlJoint L P →
    D.R.m = m → DV.NprimeDef D L → FamRec.TauNat L → FamRec.IoPrime L → 0 < D.what₂.Dall → A.e0 = R.e0 →
    SameNumbers (FamRec.famOf L m A) (famC m C P R) ∧ SameNumbers (famC m C P R) (FamRec.famOf L m A)

open Formalism.MainNotions Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost in

def CompatibleOfLocal : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ), Fm.x1 < x →
    ∀ (M : Lnk.Mod Fm x) (F : ∀ u0 : M.e.A, LChain2.Fam ((Fm.D x (M.pt u0)).what₂.Word) M.m)
      (ell : AddChar (E0 × M.e.A) ℂ → ℂ) (C : Consts) (cT : ℝ) (N : ℕ) (η θ etaB eB : ℝ),
      C.eDiv ≤ eD → C.eLoss ≤ eL → C.cHH ≤ cHH →
      TieArith Fm x M.pt M.av M.AD ell M.TT M.T2 M.a M.w →
      (Fm.L x M.i0).logDerivativeAtOne = (ell chC).re → η = (Fm.L x M.i0).etaSz →
      (∀ u0, FamRec.LocalTie (Fm.L x (M.pt u0)) M.m (F u0)) →
      LChain2.Inputs2 M.AD ell (FamRec.globM M etaB eB) C cT N M.TT M.T2 M.a M.w F η θ eK K CL →
      ChainTied Fm eD eL K cHH eK CL x

open Formalism.MainNotions Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost in

def ColumnsToCompatible : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ), Fm.x1 < x →
    ∀ (M : Lnk.Mod Fm x)
      (C : ∀ u0 : M.e.A, ColObj (Fm.D x (M.pt u0)).what₂.LL (Fm.D x (M.pt u0)).what₂.Word)
      (P : ∀ u0 : M.e.A, PlDat (Fm.D x (M.pt u0)).what₂.LL (Fm.D x (M.pt u0)).what₂.Word)
      (R : ∀ u0 : M.e.A, RowArg (C u0))
      (ell : AddChar (E0 × M.e.A) ℂ → ℂ) (Cn : Consts) (cT : ℝ) (N : ℕ) (η θ etaB eB : ℝ),
      Cn.eDiv ≤ eD → Cn.eLoss ≤ eL → Cn.cHH ≤ cHH →
      TieArith Fm x M.pt M.av M.AD ell M.TT M.T2 M.a M.w →
      (Fm.L x M.i0).logDerivativeAtOne = (ell chC).re → η = (Fm.L x M.i0).etaSz →
      (∀ u0, (C u0).RecJoint (Fm.D x (M.pt u0))) → (∀ u0, (P u0).N.R.m = M.m) → (∀ u0, PlaceDataCompatible (C u0) (P u0)) →
      (∀ u0, (Fm.D x (M.pt u0)).NuFull) → (∀ u0, RowJoint (R u0)) → (∀ u0, PlJoint (Fm.L x (M.pt u0)) (P u0)) →
      LChain2.Inputs2 M.AD ell (FamRec.globM M etaB eB) Cn cT N M.TT M.T2 M.a M.w
        (fun u0 => famC M.m (C u0) (P u0) (R u0)) η θ eK K CL →
      ChainTied Fm eD eL K cHH eK CL x

end Rec

section Conc

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}

def argPl (A : ColArg W Ch) (P : PlDat X.K Pr.Word) : ColArg W Ch :=
  ColArg.ofTau W Ch A.num (Arith.supp P.N P.Lv X.K) (fun u => Arith.sg P.N P.Cs P.Lv P.sd (P.code u))
    (Arith.tau P.N P.Cs) A.yM A.sel A.Sq

def ptC (hX : X.Ok) (A : ColArg W Ch) (P : PlDat X.K Pr.Word) (Rw : RowArg (colObj W Ch hX (argPl A P))) : Pt Pr.Word :=
  { K := X.K, i4 := hX.cplxK, C := colObj W Ch hX (argPl A P), P := P, R := Rw }

def ConcreteCompatible : Prop :=
  ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok) (A : ColArg W Ch)
    (P : PlDat X.K Pr.Word), X.f = P.N.R.f → R.k = P.N.R.k → R.m = P.N.R.m → Arith.SdOk P.N P.sd →
    (∀ u, P.code u ∈ P.Lv.Ws) → (∀ u, Pr.T u = P.Lv.T (P.code u)) →
    (∀ u w, prW w = Pr.T u → (seenC Pr u w ↔ 0 < vAdd w (Arith.elt P.sd (P.Lv.piT (P.code u))))) →
    PlaceDataCompatible (colObj W Ch hX (argPl A P)) P

def ConcArgOk : Prop :=
  ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (A : ColArg W Ch)
    (P : PlDat X.K Pr.Word), (∀ u, P.code u ∈ P.Lv.Ws) → (∀ u, Pr.T u = P.Lv.T (P.code u)) →
    (∀ u, P.N.sc.X'' P.N.R.n < (Pr.T u : ℝ)) →
    (∀ u w, prW w ∈ (argPl A P).served → Submodule.IsLattice X.K (((argPl A P).Sv u).NP w)) → (∀ τ, 0 < A.dsig τ) →
    ColArgOk W Ch (argPl A P)

def ConcFacts : Prop :=
  ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok) (A : ColArg W Ch),
    Pr.Ok → Sizes Pr W A.num.sc.a → ColArgOk W Ch A → ColOpen W Ch A → ColFacts (colObj W Ch hX A)

def ConcService : Prop :=
  ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok) (A : ColArg W Ch)
    (P : PlDat X.K Pr.Word), Pr.Ok → ColArgOk W Ch A → ColOpen W Ch A → P.Cs.admitted →
    (∀ u w, prW w ∈ A.served → (((colObj W Ch hX A).lenMN u w : ℚ) : ℝ) ≤
      ((colObj W Ch hX A).dM u : ℝ) * (Arith.tau P.N P.Cs (Arith.pOf w) + Arith.io P.N P.Cs (Arith.pOf w))) →
    Service (colObj W Ch hX A) P

def ConcOkIn : Prop :=
  ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok) (A : ColArg W Ch)
    (P : PlDat X.K Pr.Word) (Rw : RowArg (colObj W Ch hX (argPl A P))) (g₁ g₂ : ℕ) (Xpp : ℝ),
    Pr.Ok → Sizes Pr W A.num.sc.a →
    (∀ u w, prW w ∈ (argPl A P).served → Submodule.IsLattice X.K (((argPl A P).Sv u).NP w)) → (∀ τ, 0 < A.dsig τ) →
    ColOpen W Ch (argPl A P) →
    X.f = P.N.R.f → R.k = P.N.R.k → R.m = P.N.R.m → Arith.SdOk P.N P.sd →
    (∀ u, P.code u ∈ P.Lv.Ws) → (∀ u, Pr.T u = P.Lv.T (P.code u)) →
    (∀ u w, prW w = Pr.T u → (seenC Pr u w ↔ 0 < vAdd w (Arith.elt P.sd (P.Lv.piT (P.code u))))) →
    P.N.g 0 = g₁ → P.N.g 1 = g₂ → P.N.sc.X'' P.N.R.n = Xpp →
    (∀ u, P.N.sc.X'' P.N.R.n < (Pr.T u : ℝ)) → DatWin P → P.Cs.admitted →
    (∀ u w, prW w ∈ (argPl A P).served → (((colObj W Ch hX (argPl A P)).lenMN u w : ℚ) : ℝ) ≤
      ((colObj W Ch hX (argPl A P)).dM u : ℝ) * (Arith.tau P.N P.Cs (Arith.pOf w) + Arith.io P.N P.Cs (Arith.pOf w))) →
    (ptC hX A P Rw).OkIn R.m X.f g₁ g₂ Xpp

end Conc

section Dat

structure DataCompatible {X : Fields} {Pr : Primes X} (P : PlDat X.K Pr.Word) (W : Wts X Pr.Word P.N.R) (num : ScNum) where
  ρ : X.Tau ≃ RPl P.N.R
  sd : Arith.SdOk P.N P.sd
  code : ∀ u, P.code u ∈ P.Lv.Ws
  T : ∀ u, Pr.T u = P.Lv.T (P.code u)
  g : ∀ i, Pr.g i = P.N.g i
  cond : Pr.cond = P.N.cond
  piT : ∀ u τ, ((X.embO τ (Pr.piT u) : 𝓞 X.K) : X.K) = Arith.elt P.sd (P.Lv.piT (P.code u))
  piG : ∀ i τ, ((X.embO τ (Pr.piG i) : 𝓞 X.K) : X.K) = Arith.elt P.sd (P.Lv.piG i)
  tops : ∀ τ, τ ∈ W.tops ↔ ((ρ τ).1 = false ∧ (ρ τ).2 ∈ P.N.TT)
  hc_u : ∀ u τ i, (W.hc u τ).u i = P.N.uW (P.code u) (ρ τ) i
  hc_v : ∀ u τ, (W.hc u τ).v = (P.N.hc (ρ τ)).v
  hc_b : ∀ u τ, (W.hc u τ).b = (P.N.hc (ρ τ)).b
  hc_e : ∀ u τ, (W.hc u τ).e = (P.N.hc (ρ τ)).e
  sc : num.sc = P.N.sc
  Sc : num.Sc = P.N.Sc
  eta : num.eta = P.N.eta
  v : vC X = P.N.v

def DataToCompatible : Prop :=
  ∀ {X : Fields} {Pr : Primes X} (P : PlDat X.K Pr.Word) (W : Wts X Pr.Word P.N.R) (Ch : Chars X Pr P.N.R.m) (hX : X.Ok)
    (A : ColArg W Ch), Pr.Ok → DataCompatible P W A.num → PlaceDataCompatible (colObj W Ch hX (argPl A P)) P

end Dat

section ConcNum

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

structure GlobTied {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (num : ScNum) (G : Glob) (TT : Finset H)
    (a : H → ℝ) (w : Fin R.m → E0 × H → ℝ) where
  σ : X.Tau ≃ ↥(PhiSet (H := H))
  x : num.sc.x = G.x
  ε : num.sc.eps = G.ε
  k : (R.k : ℝ) = G.k
  v : vC X = G.v
  lg : ∑ i, Real.log (Pr.g i : ℝ) = G.lg
  tops : W.tops = TT.map ((LChain6.topPhi H).trans σ.symm.toEmbedding)
  aTop : ∀ u, ∀ t ∈ TT, (W.aTop u (σ.symm (LChain6.topPhi H t)) : ℝ) = a t
  row : ∀ j τ, (((W.row τ).e j : ℚ) : ℝ) = w j (σ τ).1

def ConcZNum : Prop :=
  ∀ {Wd : H → Type} [∀ u0, Fintype (Wd u0)] {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (num : ScNum)
    (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin R.m → E0 × H → ℝ) (Fm : ∀ u0, Fam (Wd u0) R.m) (u0 : H), GlobTied W num G TT a (w u0) →
    ∀ (u : Pr.Word) (c : ℝ),
      SectionsFourToSixTransfer.ZiiR (mkData G cHH D ell N TT T2 a w Fm) c num.Sc num.sc.L (Real.log (Pr.T u : ℝ)) =
        ZiiC W u c num.sc.a num.sc.b' num.sc.L num.Sc ∧
      SectionsFourToSixTransfer.ZiiiR (mkData G cHH D ell N TT T2 a w Fm) c num.Sc num.sc.L (Real.log (Pr.T u : ℝ)) =
        ZiiiC W u c num.sc.a num.sc.b' num.sc.L num.Sc

def ConcXNum : Prop :=
  ∀ {Wd : H → Type} [∀ u0, Fintype (Wd u0)] {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (num : ScNum)
    (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin R.m → E0 × H → ℝ) (Fm : ∀ u0, Fam (Wd u0) R.m) (u0 : H), GlobTied W num G TT a (w u0) →
    xLowC W num = SectionsFourToSixTransfer.mainCount (mkData G cHH D ell N TT T2 a w Fm) u0 - 11 * Real.log (bTx G.x G.ε) ∧
    ∀ c5 : ℝ, 15 + 3 * num.CY ≤ c5 → 3 ≤ c5 → 2 ≤ R.k → 1 ≤ Real.log G.k →
      xUpC R num ≤ c5 * (R.m : ℝ) * Real.log (bTx G.x G.ε) ∧ xVarC R ≤ c5 * Real.log G.k

def ConcXExact : Prop :=
  ∀ {Wd : H → Type} [∀ u0, Fintype (Wd u0)] {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (num : ScNum)
    (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin R.m → E0 × H → ℝ) (Fm : ∀ u0, Fam (Wd u0) R.m) (u0 : H), GlobTied W num G TT a (w u0) →
    ∀ (bN : H → Fin R.m → Fin (PhiSet (H := H)).card → ℝ) (cE5 : ℝ),
      SectionsFourToSixTransfer.ExactWindows (mkData G cHH D ell N TT T2 a w Fm) bN → G.lg ≤ 18 * Real.log (bTx G.x G.ε) + 2 →
      (R.m : ℝ) ^ 2 ≤ G.k → (∀ j ρ, 1 ≤ bN u0 j ρ ∧ bN u0 j ρ ≤ w u0 j (ePhi ρ)) → 20 ≤ cE5 →
      SectionsFourToSixTransfer.exactMain (mkData G cHH D ell N TT T2 a w Fm) bN u0 - cE5 * Real.log (bTx G.x G.ε) - 1 ≤ xLowC W num

def ConcLam : Prop :=
  ∀ {Wd : H → Type} [∀ u0, Fintype (Wd u0)] {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (num : ScNum)
    (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin R.m → E0 × H → ℝ) (Fm : ∀ u0, Fam (Wd u0) R.m) (u0 : H) (T : GlobTied W num G TT a (w u0))
    (u : Pr.Word) (aM : ℝ) (Wt bt : TT → ℝ), (∀ t ∈ TT, a t ≤ aM) →
    (∀ t : TT, (WtauC W u (T.σ.symm (LChain6.topPhi H t)) : ℝ) ≤ Wt t) → (∀ t, 0 ≤ bt t) →
    lambdaConstant W u ≤ SectionsFourToSixTransfer.lambdaIndex (mkData G cHH D ell N TT T2 a w Fm) aM Finset.univ Wt bt

end ConcNum

end Formalism.L2.GlobalTheoryTheory.FamCol

end
