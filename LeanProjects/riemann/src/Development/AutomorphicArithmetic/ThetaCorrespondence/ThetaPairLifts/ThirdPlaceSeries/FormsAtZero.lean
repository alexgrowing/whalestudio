import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins

set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop
section Alg
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}
end Alg
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
abbrev rJ_z : Set (GA D (D.sp.Y 0)) :=
  levS (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))
abbrev realCharacter : GA D (D.sp.Y 0) → ℂ :=
  Formalism.IndefR.Lev.levChi (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))
abbrev BaseRowSpace : Submodule ℂ (SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) := MultT W.Q.Rl.θ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)
def rowFormOfVector (e : W.Q.Rl.HE.H) : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := PiTensorProduct.lift (W.Q.Rl.HE.e e)
def rowFormOfTuple (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  _root_.GlobalTheory.MiTop.rowFormOfVector W (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)))
abbrev formsAtZero (u : D.what₂.Word) : Formalism.L2.Forms.Forms0 D u := (W.R.T.cols.forms u).to0
structure BottomData (u : D.what₂.Word) where
  B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)
  b : GA D (D.sp.Y 0)
  a₀ : GA D (D.sp.X 0)
  a : GA D (D.sp.X 0)
  k : GA D (D.sp.Y 0)
variable {W}
structure BottomData.Pin {u : D.what₂.Word} (d : _root_.GlobalTheory.MiTop.BottomData W u) (z : GA D (D.sp.Y 0)) : Prop where
  adapted : d.B.Adapted (W.S.tr u).wt
  h0 : IsTransportAdelicCorrection (W.S.tr u) d.a₀
  fin : d.a ∈ GfC (D.sp.X 0)
  cen : d.a ∈ Subgroup.center (GA D (D.sp.X 0))
  lev : d.k ∈ _root_.GlobalTheory.MiTop.rJ_z W
  eq : embA d.B.d d.B.o (d.a₀ * d.a) * d.b =
    (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k)
def BottomData.per {u : D.what₂.Word} (d : _root_.GlobalTheory.MiTop.BottomData W u) (φ : D.what₂.Mu u)
    (T : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) (y : (D.mem u).C.Y 0) (v : SmT (W.Q.Rl.MY 0)) : ℂ :=
  d.B.lev.per W.Q.Rl.ψ ((chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) (rTrans d.b (T v))
def BottomData.Rel {u : D.what₂.Word} (d : _root_.GlobalTheory.MiTop.BottomData W u) (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (c : W.P.T → ℂ) : Prop :=
  ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∃ p : D.what₂.Mu u → ℂ, ∀ (φ₀ φ : D.what₂.Mu u) (t : W.P.T)
    (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
    (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ α α' : ℂ,
    α * p φ₀ + α' * (c t * D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))) = 0 →
      ∀ y v, α * d.per (U φ₀) T y v + α' * d.per (U φ) (_root_.GlobalTheory.MiTop.rowFormOfTuple W t F') y v = 0
variable (W)
def UnitCoefficients (c : W.P.T → ℂ) : Prop :=
  (∀ t, c t ≠ 0) ∧ ∀ w (k : D.what₂.LL), D.what₂.embLL k = c (W.Q.Rl.mu w) / c W.P.A3.A.μ0 → vw w k = 0
def JointCondition : Prop :=
  ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u, ∃ (d : _root_.GlobalTheory.MiTop.BottomData W u) (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ)
    (c : W.P.T → ℂ), d.Pin z ∧ 0 < r ∧ (∀ φ, ‖U φ‖ = r * ‖φ‖) ∧ _root_.GlobalTheory.MiTop.UnitCoefficients W c ∧ d.Rel U c
def IsPairing' (u : D.what₂.Word) (t : GA D (D.sp.Y 0)) (f : GA D (D.sp.Y 0) → ℂ) (T : Cu W.S.X u W.S.Y.hK) (b : ℂ) : Prop :=
  ∃ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq t f ∧
    b = ⟪star φ, PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) T⟫_ℂ
structure BottomHypotheses : Prop where
  hyp : _root_.GlobalTheory.MiS.HypothesisAtPackage W
  pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation W.Q
  see : _root_.Formalism.IndefR.IndefiniteRealisationExtends W.Q
  used : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t)
  idE : GlobalTheory.Core.Mi.IdE W.S.X
  gap : GlobalTheory.Count.GapGe W.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  fin : Formalism.L2.SG.PackageTie2.FinX W.S.Y
def columnOfCoordinates (u : D.what₂.Word) (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) : D.what₂.Mu u :=
  ∑ i, x i • D.jN u (W.P.I.eNu u (Pi.single i 1))
def ColumnCoordinateCondition : Prop :=
  ∀ u, Function.Bijective (_root_.GlobalTheory.MiTop.columnOfCoordinates W u) ∧ (∀ x, _root_.GlobalTheory.MiTop.columnOfCoordinates W u (cpt D.what₂.embLL x) = D.jN u (W.P.I.eNu u x)) ∧
    ∃ r : ℝ, 0 < r ∧ ∀ x, fnorm (W.P.Dc.Xc (W.P.I.wU u) W.P.A3.fam3.base3.v0)
      (Formalism.L2.SG.JoinSI.cjv (Formalism.L2.SG.JoinSI.twQ W.P) x) = r * ‖_root_.GlobalTheory.MiTop.columnOfCoordinates W u x‖
def IsColumnForm (u : D.what₂.Word) (T : Cu W.S.X u W.S.Y.hK) (φ : D.what₂.Mu u) : Prop :=
  Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK T = (D.eMu u φ).1
def PairingFormCondition (v : (W.Q.Rl.MY 0).Vec) : Prop :=
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ e ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EEl true, ∀ (u : D.what₂.Word) (m : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Mem), HEq m (W.P.I.wU u) →
    ∀ (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) (x' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.a m) → ℂ), HEq x x' →
    ∀ T b, _root_.GlobalTheory.MiTop.IsColumnForm W u T (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x) →
      _root_.GlobalTheory.MiTop.IsPairing' W u (show GA D (D.sp.Y 0) from W.Q.tS) (_root_.GlobalTheory.MiTop.rowFormOfVector W (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) e) (PiTensorProduct.tprod ℂ v)) T b →
      ⟪W.Q.sEE e, (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Sp.Pu m (Formalism.L2.SG.JoinSI.cjv (Formalism.L2.SG.JoinSI.twQ W.P) x')⟫_ℂ =
        cj (Formalism.L2.SG.JoinSI.twQ W.P) (κ * b)
def IsShiftOperator (z : GA D (D.sp.Y 0)) (V : W.Q.Rl.HE.H →ₗ[ℂ] W.Q.Rl.HE.H) : Prop :=
  (∀ e v, _root_.GlobalTheory.MiTop.rowFormOfVector W (V e) v = rTrans (show GA D (Yc D 0) from z) (_root_.GlobalTheory.MiTop.rowFormOfVector W e v)) ∧ (∀ e, ‖V e‖ = ‖e‖) ∧
    ∀ e, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) →
      W.Q.Rl.HE.e (V e) ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)
def BottomRelation (z : GA D (D.sp.Y 0)) {u : D.what₂.Word} (d : _root_.GlobalTheory.MiTop.BottomData W u) : Prop :=
  ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ (φ φ' : D.what₂.Mu u), ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ T' ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ α α' : ℂ,
    (∀ y v, α * d.per φ T y v + α' * d.per φ' T' y v = 0) →
    ∀ (v : SmT (W.Q.Rl.MY 0)) C C' b b', _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → _root_.GlobalTheory.MiTop.IsColumnForm W u C' (R φ') →
      _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T v) C b →
      _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T' v) C' b' → α * b + α' * b' = 0
end GlobalTheory.MiTop
namespace GlobalTheory.MiTop
end GlobalTheory.MiTop
end
end
