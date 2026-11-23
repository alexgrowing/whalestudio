import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct InnerProductSpace
open IsDedekindDomain NumberField MeasureTheory

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Zero

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : Mult.DSModel V S)

end Zero

section FromLinks

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def TopMultH (R : RealDat D A Ks) : Prop :=
  ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
    Mult.MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))

def datXP (R : RealDat D A Ks) (t : T) (P : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) : Formalism.L2.DIV.LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q t) P R.chi (R.xiR t) Frm.B

open Classical in

def SsetF (R : RealDat D A Ks) (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Sb ∪ R.Q t).image (Formalism.L2.DIV.underPl D.host.F)

def toChainReal (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) :
    ChainReal D where
  θ := R.θ
  ψ := R.ψ
  η := R.eta
  Ptw := Ptw D
  Y := Yc D
  SY j := Mult.parB (Ptw D) (min j D.R.m)
  MY := R.MY
  X := D.sp.X'
  MX := R.MX
  J _ μ j := if j < D.R.m then levS _ (R.βY j) (R.datYt (tupT μ) j R.triv) else Set.univ
  χ _ μ j := if j < D.R.m then levChi _ (R.βY j) (R.datYt (tupT μ) j R.triv) else 0
  JX _ μ := levS _ R.βX (R.datXt (tupT μ))
  χX _ μ := levChi _ R.βX (R.datXt (tupT μ))
  meas _ μ j := R.νY (tupT μ) j
  fd μ j := R.fdY (tupT μ) j
  measX _ μ := R.νX (tupT μ)
  fdX μ := R.fdX (tupT μ)
  measE b := ENNReal.ofReal (RealDat.nP F b)⁻¹ • R.ν0
  fdE := R.fd0
  chr μ := R.toLevCh.mu (tupT μ)
  Sinf k := PolF D (Yc D (k + 1)).rank (Yc D k).rank
  pt _ μ k := R.ptY (tupT μ) k
  It := R.ItY
  th μ k := thetaKO (R.ωY (tupT μ) k)
  ioC _ μ k := if h : k + 1 < D.R.m then
      (LinearEquiv.ofEq _ _ (by simp only [if_pos (show k < D.R.m by omega)])).toLinearMap ∘ₗ
        R.ioY (tupT μ) k ∘ₗ (LinearEquiv.ofEq _ _ (by simp only [if_pos h])).toLinearMap
    else 0
  SinfX := PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank
  ptX _ μ := R.ptX (tupT μ)
  ItX := R.ItX
  thX μ := thetaKO (R.ωX (tupT μ))
  ioX _ μ := (LinearEquiv.ofEq _ _ (by simp only [if_pos (show D.R.m - 1 < D.R.m by omega)])).toLinearMap ∘ₗ
    R.ioX (tupT μ) ∘ₗ (LinearEquiv.ofEq _ _ (hTop (tupT μ)).symm).toLinearMap
  JE b := levS _ (R.βY 0) (R.dat0 (R.levR F b))
  χE b := levChi _ (R.βY 0) (R.dat0 (R.levR F b))
  eE _ := R.e0
  Sb := SsetF R (tupT D.what₂.mu0)
  volTop := 1
  JP b μ j := if j < D.R.m then levS _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b)) else Set.univ
  χP b μ j := if j < D.R.m then levChi _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b)) else 0
  JXP b μ := levS _ R.βX (datXP R (tupT μ) (R.levR F b))
  χXP b μ := levChi _ R.βX (datXP R (tupT μ) (R.levR F b))
  nrm b := (RealDat.nP F b)⁻¹

def levSubV (V : HSp D) (W : Type) [AddCommGroup W] [Module ℂ W] (J : Set (GA D V)) (χ : GA D V → ℂ) :
    Submodule ℂ (GA D V → W) where
  carrier := {F | ∀ k ∈ J, ∀ g, F (g * k) = χ k • F g}
  add_mem' {F F'} hF hF' k hk g := by simp only [Pi.add_apply, hF k hk g, hF' k hk g, smul_add]
  zero_mem' k _ g := by simp
  smul_mem' c F hF k hk g := by simp only [Pi.smul_apply, hF k hk g, smul_comm c (χ k)]

def datVP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) :
    Formalism.L2.DIV.LevDat D.host.E ℂ (Vc D i).rank :=
  datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg (R.Q t) P (fun _ => R.chi ((i : ℕ) + 1)) (R.xiR t) Frm.A

def ipVia {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N] (e : H →ₗ[ℂ] N)
    (x y : N) : ℂ := by
  classical
  exact if h : x ∈ LinearMap.range e ∧ y ∈ LinearMap.range e then ⟪h.1.choose, h.2.choose⟫_ℂ else 0

def toLiftReal (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) :
    LiftReal D (toChainReal R F tupT hm hTop) where
  V := Vc D
  W := Wc D
  κ i := kapAt (Wc D i) (sg0 D A)
  SW i := parAt (Wc D i) (sg0 D A)
  MW i := R.MW i (sg0 D A)
  JW i := levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  χW i := levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  eW i := R.eWf i (sg0 D A)
  JA i := levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  χA i := levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  measW i := ENNReal.ofReal (RealDat.nP F false)⁻¹ • R.νW i
  fdW i := R.fdW i
  SbW := SsetF R (tupT D.what₂.mu0)
  TauV i := (R.cV i).W
  Amt μ i := LinearMap.range (R.extV i (tupT μ)) ⊓
    levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i (tupT μ) (R.levR F false)))
      (levChi _ (R.βV i) (datVP R i (tupT μ) (R.levR F false)))
  ipA μ i := fun x y => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ)) x y
  measV μ i := R.νV i (tupT μ)
  fdV μ i := R.fdV i (tupT μ)
  TK i := LowT (R.MW i (sg0 D A))
  embK i := PiTensorProduct.map fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype
  Sinf' i := PolF D (Wc D i).rank (Vc D i).rank
  ioK i := R.ioP i
  ptW μ i := R.ptP i (tupT μ)
  thW μ i := fun g h f => thetaKO (R.ωP i (tupT μ)) h g f
  thC μ i := LinearMap.lcomp ℂ (GA D (Wc D i) → ℂ) (PiTensorProduct.map fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) ∘ₗ
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ R.thF i (tupT μ) ∘ₗ
    (LinearEquiv.ofInjective _ (hinj i (tupT μ))).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left

structure RecReal (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t))
    (X0 : BaseLevelRowSide D) (Ish : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true)
    (I0 : RowIds X0.s (toChainReal R F tupT hm hTop) false)
    (IL : LiftIds (toLiftReal R F tupT hm hTop hinj)) (K : ColReal D) {Xd : DivX D} (E : EigIdx D Xd)
    (labPi : E.Pi → A.fam.base.Ix) {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n)
    (eFT : D.what₂.FT ≃ principalLevelFrame.FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0))
    (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (ι : ∀ i, ↥(GfC (Yc D 0)) →* ↥(GfC (Wc D i))) (nch : NChoice D)
    (Tp : Formalism.L2.Host.TupTied D R.C nch) : Prop where

  base : R.BaseW F

  tied : RecTied D X0 (toChainReal R F tupT hm hTop) Ish I0 (toLiftReal R F tupT hm hTop hinj) IL K

  prtE : ∀ π, Ish.prt π = (principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true)))
    (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) R.e0 (principalLevelFrame.rowRepR R.θ (eFT π))).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

  prtE0 : ∀ π, I0.prt π = (principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F false)))
    (levChi _ (R.βY 0) (R.dat0 (R.levR F false))) R.e0 (principalLevelFrame.rowRepR R.θ (eFT π))).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

  prtWE : ∀ i π, IL.prtW i π = (principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A))
    (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))
    (R.eWf i (sg0 D A)) (principalLevelFrame.rowRepR R.θ (eFT π))).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap

  xi : ∀ μ, Used0 D μ → K.xi μ = R.toLevCh.xi (tupT μ)

  tupXi : ∀ μ, Used0 D μ → R.toLevCh.xiH (tupT μ) = Tp.xi μ

  tupAt : ∀ w, tupT (D.what₂.muAt w) = R.mu (D.plEq w)

  isomFin : ∀ i, principalLevelFrame.IsIsomFin (ι i)

  frameMatch : ∀ i, principalLevelFrame.FrameMatch PY (PW i) (ι i)

end FromLinks

end Formalism.IndefR.RecTie

end
