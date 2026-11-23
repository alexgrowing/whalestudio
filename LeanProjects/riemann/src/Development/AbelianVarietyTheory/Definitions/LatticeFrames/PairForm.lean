import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CxTiesOf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses
import Formalism.LocalToGlobal.IndefiniteReal.RealPins

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

def Anchored (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ)
    (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  ∀ u, ∃ p b : ℂ, p ≠ 0 ∧ b ≠ 0 ∧ ∀ t (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K),
    c u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) * b =
      p * ⟪sEE (V (X.Θ t (X.jR t (eV t F)))), (fc X.zs).Sp.Pu u ((U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def UnitAt (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  (∀ u t, c u t ≠ 0) ∧ ∀ u w (k : K), Bs.v0.embedding k = c u (X.μ w) / c u Bs.μ0 → vw w k = 0

end Alg

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

abbrev rJ : Set (GA D (D.sp.Y 0)) :=
  levS (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

abbrev rChi : GA D (D.sp.Y 0) → ℂ :=
  Formalism.IndefR.Lev.levChi (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

abbrev ThetaLiftSpaceZero : Submodule ℂ (SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) := MultT W.Q.Rl.θ (W.Q.Rl.MY 0) (rJ W) (rChi W)

def rowOf (e : W.Q.Rl.HE.H) : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := PiTensorProduct.lift (W.Q.Rl.HE.e e)

def rowAt (t : W.P.T) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  rowOf W (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (cxW W).zs t F)))

abbrev F0 (u : D.what₂.Word) : Formalism.L2.Forms.Forms0 D u := (W.R.T.cols.forms u).to0

structure BotDat (u : D.what₂.Word) where
  B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)
  b : GA D (D.sp.Y 0)
  a₀ : GA D (D.sp.X 0)
  a : GA D (D.sp.X 0)
  k : GA D (D.sp.Y 0)

variable {W}

structure BotDat.Pin {u : D.what₂.Word} (d : BotDat W u) (z : GA D (D.sp.Y 0)) : Prop where
  adapted : d.B.Adapted (W.S.tr u).wt
  h0 : IsTransportAdelicCorrection (W.S.tr u) d.a₀
  fin : d.a ∈ GfC (D.sp.X 0)
  cen : d.a ∈ Subgroup.center (GA D (D.sp.X 0))
  lev : d.k ∈ rJ W
  eq : embA d.B.d d.B.o (d.a₀ * d.a) * d.b =
    (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k)

def BotDat.per {u : D.what₂.Word} (d : BotDat W u) (φ : D.what₂.Mu u)
    (T : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) (y : (D.mem u).C.Y 0) (v : SmT (W.Q.Rl.MY 0)) : ℂ :=
  d.B.lev.per W.Q.Rl.ψ ((chart0 (F0 W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) (rTrans d.b (T v))

def BotDat.Rel {u : D.what₂.Word} (d : BotDat W u) (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (c : W.P.T → ℂ) : Prop :=
  ∀ T ∈ ThetaLiftSpaceZero W, ∃ p : D.what₂.Mu u → ℂ, ∀ (φ₀ φ : D.what₂.Mu u) (t : W.P.T)
    (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
    (F' : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ α α' : ℂ,
    α * p φ₀ + α' * (c t * D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))) = 0 →
      ∀ y v, α * d.per (U φ₀) T y v + α' * d.per (U φ) (rowAt W t F') y v = 0

variable (W)

def UnitC (c : W.P.T → ℂ) : Prop :=
  (∀ t, c t ≠ 0) ∧ ∀ w (k : D.what₂.LL), D.what₂.embLL k = c (W.Q.Rl.mu w) / c W.P.A3.A.μ0 → vw w k = 0

def Joint : Prop :=
  ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u, ∃ (d : BotDat W u) (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ)
    (c : W.P.T → ℂ), d.Pin z ∧ 0 < r ∧ (∀ φ, ‖U φ‖ = r * ‖φ‖) ∧ UnitC W c ∧ d.Rel U c

def IsPair (u : D.what₂.Word) (t : GA D (D.sp.Y 0)) (f : GA D (D.sp.Y 0) → ℂ) (T : Cu W.S.X u W.S.Y.hK) (b : ℂ) : Prop :=
  ∃ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq t f ∧
    b = ⟪star φ, PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) T⟫_ℂ

structure BotHyp : Prop where
  hyp : HypAt W
  pins : RealPins W.Q
  see : SeeEx W.Q
  used : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t)
  idE : GlobalTheory.Core.Mi.IdE W.S.X
  gap : GlobalTheory.Count.GapGe W.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  fin : Formalism.L2.SG.PackageTie2.FinX W.S.Y

def colC (u : D.what₂.Word) (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) : D.what₂.Mu u :=
  ∑ i, x i • D.jN u (W.P.I.eNu u (Pi.single i 1))

def ColCrd : Prop :=
  ∀ u, Function.Bijective (colC W u) ∧ (∀ x, colC W u (cpt D.what₂.embLL x) = D.jN u (W.P.I.eNu u x)) ∧
    ∃ r : ℝ, 0 < r ∧ ∀ x, fnorm (W.P.Dc.Xc (W.P.I.wU u) W.P.A3.fam3.base3.v0)
      (Formalism.L2.SG.JoinSI.cjv (Formalism.L2.SG.JoinSI.twQ W.P) x) = r * ‖colC W u x‖

def IsCol (u : D.what₂.Word) (T : Cu W.S.X u W.S.Y.hK) (φ : D.what₂.Mu u) : Prop :=
  Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK T = (D.eMu u φ).1

def PairForm (v : (W.Q.Rl.MY 0).Vec) : Prop :=
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ e ∈ (cxW W).EEl true, ∀ (u : D.what₂.Word) (m : (W.Q.F.fc (cxW W).zs).Dc.Mem), HEq m (W.P.I.wU u) →
    ∀ (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) (x' : Fin ((W.Q.F.fc (cxW W).zs).Dc.a m) → ℂ), HEq x x' →
    ∀ T b, IsCol W u T (colC W u x) →
      IsPair W u (show GA D (D.sp.Y 0) from W.Q.tS) (rowOf W (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) e) (PiTensorProduct.tprod ℂ v)) T b →
      ⟪W.Q.sEE e, (W.Q.F.fc (cxW W).zs).Sp.Pu m (Formalism.L2.SG.JoinSI.cjv (Formalism.L2.SG.JoinSI.twQ W.P) x')⟫_ℂ =
        cj (Formalism.L2.SG.JoinSI.twQ W.P) (κ * b)

def IsShift (z : GA D (D.sp.Y 0)) (V : W.Q.Rl.HE.H →ₗ[ℂ] W.Q.Rl.HE.H) : Prop :=
  (∀ e v, rowOf W (V e) v = rTrans (show GA D (Yc D 0) from z) (rowOf W e v)) ∧ (∀ e, ‖V e‖ = ‖e‖) ∧
    ∀ e, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) →
      W.Q.Rl.HE.e (V e) ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)

def BotRel (z : GA D (D.sp.Y 0)) {u : D.what₂.Word} (d : BotDat W u) : Prop :=
  ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ (φ φ' : D.what₂.Mu u), ∀ T ∈ ThetaLiftSpaceZero W, ∀ T' ∈ ThetaLiftSpaceZero W, ∀ α α' : ℂ,
    (∀ y v, α * d.per φ T y v + α' * d.per φ' T' y v = 0) →
    ∀ (v : SmT (W.Q.Rl.MY 0)) C C' b b', IsCol W u C (R φ) → IsCol W u C' (R φ') →
      IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T v) C b →
      IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T' v) C' b' → α * b + α' * b' = 0

end GlobalTheory.MiTop

namespace GlobalTheory.MiTop

def PuNZ (D : D7) : Prop :=
  ∀ u, ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0

end GlobalTheory.MiTop

end
