import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
import Formalism.LocalToGlobal.IndefiniteReal.TensCastR
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPToLiftReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResInjLToLiftReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAdjointAtLiftEqLowestKTypeRestriction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.MainNotions.N IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NJoin

abbrev tensCast {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := Formalism.IndefR.principalLevelFrame.tensCastR h

abbrev StdFrame {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : RowPsi V n) : Prop :=
  Formalism.IndefR.principalLevelFrame.StdPsi hF P

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RealAt (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) : Type 1 where
  G : Type
  [grp : Group G]
  [fin : Fintype G]
  Pl0 : Type
  T : Type
  A : FamIn D.what₂.LL G Pl0 T D.R.m
  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]
  R : RealDat D A Ks
  F : Face D A
  tupT : D.what₂.Tup → T
  hm : 0 < D.R.m
  hTop : TopMultH R
  hinj : ∀ i t, Function.Injective (R.extV i t)
  X0 : BaseLevelRowSide D
  Ish : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true
  I0 : RowIds X0.s (toChainReal R F tupT hm hTop) false
  IL : LiftIds (toLiftReal R F tupT hm hTop hinj)
  K : ColReal D
  Xd : DivX D
  E : EigIdx D Xd
  labPi : E.Pi → A.fam.base.Ix
  PY : RowPsi (Yc D 0) D.R.r
  PW : ∀ i, RowPsi (Wc D i) D.R.r
  eFT : D.what₂.FT ≃ FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0)
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  ι : ∀ i, ↥(GfC (Yc D 0)) →* ↥(GfC (Wc D i))
  Tp : TupTied D R.C nch
  cfEq : R.C = cf
  tpEq : HEq Tp tp
  recR : RecReal R F tupT hm hTop hinj X0 Ish I0 IL K E labPi PY PW eFT piOf ι nch Tp
  given : GlobalTheory.LiftRows.Given R F
  full : R.FullP

attribute [instance] RealAt.grp RealAt.fin RealAt.fKs RealAt.nKs RealAt.aKs

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : RealAt D cf nch tp)

theorem RealAt.fire : ThetaFireRow (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj) X.IL :=
  ⟨fun μ _ i => GlobalTheory.ThetaPRead.isThetaP_toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj X.given.core.thP.thF μ i,
    GlobalTheory.ThetaFireLift.thetaFireL X.R X.F X.tupT X.hm X.hTop X.hinj X.given.core.lev X.given.core.grp X.given.core.models
      X.given.core.thP X.R.hv0 X.IL,
    GlobalTheory.LiftResInj.resInjL_toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj X.given.core.models.inf⟩

def RealAt.fn {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) :
    GA D (Vc D j) → (X.R.cV j).W := (X.IL.jMt μ hμ j x).1

def RealAt.rep (σ : D.what₂.FT) : NG.FinTyp D.host.E D.R.r := rowRepR X.R.θ (X.eFT σ)

structure Agree (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) where
  hF : D.host.F = maximalRealSubfield D.host.E
  PV : ∀ j, RowPsi (Vc D j) D.R.nV
  stdV : ∀ j, StdFrame hF (PV j)
  stdW : ∀ j, StdFrame hF (X.PW j)
  a : Fin D.R.m → Formalism.AUTREP.GAf D.host.E D.R.nV
  rat : ∀ j h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
    ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D j), finHom (Vc D j) γ = finHom (Vc D j) ((PV j).ψ ((a j)⁻¹ * h * a j))
  eW : ∀ μ, Used0 D μ → ∀ j : Fin D.R.m, (X.R.cV j).W ≃ₗ[ℂ] (M μ (j.1 + 1) (by omega) (by omega)).wt.W
  wt : ∀ μ hμ (j : Fin D.R.m) (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D j),
    finHom (Vc D j) γ = finHom (Vc D j) ((PV j).ψ ((a j)⁻¹ * h * a j)) → ∀ v,
      eW μ hμ j ((X.R.cV j).ρ γ v) = (M μ (j.1 + 1) (by omega) (by omega)).wt.ρ h (eW μ hμ j v)
  real : ∀ μ hμ (j : Fin D.R.m) x h,
    (M μ (j.1 + 1) (by omega) (by omega)).real x h = eW μ hμ j (X.fn hμ j x ((PV j).ψ ((a j)⁻¹ * h)))
  rep_iso : RowRepTie rep X.R.θ X.PY (X.R.MY 0) (fun b => levS _ (X.R.βY 0) (X.R.dat0 (X.R.levR X.F b)))
    (fun b => levChi _ (X.R.βY 0) (X.R.dat0 (X.R.levR X.F b))) (fun _ => X.R.e0) X.eFT

def IsCanon {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (j : Fin D.R.m) {j' : ℕ} (hj : j.1 + 1 = j')
    (Y : GlobalTheory.NPin.RowMod D rep j') : Prop :=
  ∃ (e : Y.A →ₗ[ℂ] Mult.MMap (X.R.MW j (sg0 D X.A))) (c : ℝ), Function.Injective e ∧ 0 < c ∧
    Y.C.map e = Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) ∧
    (∀ h x, e (Y.ρ h x) = actM (X.PW j) (X.R.MW j (sg0 D X.A)) h (e x)) ∧
    (∀ x ∈ Y.C, ∀ y ∈ Y.C, Y.B x y = (c : ℂ) * Mult.ipM (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) (e x) (e y)) ∧
    ∀ y : D.what₂.Mj (j.1 + 1), PiTensorProduct.lift (e (Y.φ (hj ▸ y))) = (X.IL.jMj j y).1

def OnGood (i : D.nd.Loc) (p : ∀ (j : Fin D.R.m) (t : X.T), (X.R.HV j t).H → Prop) : Prop :=
  ∀ (hμ : Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i,
    ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x →
      ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → p j (X.tupT (D.nd.mu i)) y

def EigString (i : D.nd.Loc) : Prop :=
  OnGood X i fun j t y => y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j t h →
    ∃ s, GlobalTheory.DownLift.HasString X.R j t s ∧ GlobalTheory.DownLift.IsEigV X.R j t h s y

def EigGood (i : D.nd.Loc) : Prop := OnGood X i fun j t y => GlobalTheory.DownLift.GoodVt X.R j t y

theorem used_mu (i : D.nd.Loc) : Used0 D (D.nd.mu i) :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem RealAt.existsUnique_vec {μ} (hμ : Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1)) :
    ∃! y, X.R.extV j (X.tupT μ) y = X.fn hμ j f := by
  have h : ∃ y, X.R.extV j (X.tupT μ) y = X.fn hμ j f := (X.IL.jMt μ hμ j f).2.1
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy, fun z hz => X.hinj _ _ (hz.trans hy.symm)⟩

theorem RealAt.fn_injective {μ} (hμ : Used0 D μ) (j : Fin D.R.m) : Function.Injective (X.fn hμ j) :=
  Subtype.val_injective.comp (X.IL.jMt μ hμ j).injective

theorem OnGood.mono {X : RealAt D cf nch tp} {i : D.nd.Loc} {p q : ∀ (j : Fin D.R.m) (t : X.T), (X.R.HV j t).H → Prop}
    (h : OnGood X i p) (hpq : ∀ j t y, p j t y → q j t y) : OnGood X i q :=
  fun hμ j hj x hx f hf y hy => hpq _ _ _ (h hμ j hj x hx f hf y hy)

theorem Agree.iso_rep {X : RealAt D cf nch tp} {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (A : Agree X M rep)
    (σ : D.what₂.FT) : (rep σ).Iso (X.rep σ) := A.rep_iso σ

example {μ} (hμ : Used0 D μ) (j : Fin D.R.m) : X.fn hμ j 0 = 0 :=
  congrArg Subtype.val (map_zero (X.IL.jMt μ hμ j))

example (i : D.nd.Loc) (x) (hx : x ∈ ZgoodN D.nd D.naut i) : ¬ OnGood X i fun _ _ _ => False := fun h => by
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have e : j.1 + 1 = D.nd.j i := by show D.nd.j i - 1 + 1 = _; omega
  obtain ⟨y, hy, -⟩ := X.existsUnique_vec (used_mu i) j 0
  refine h (used_mu i) j e x hx 0 ?_ y hy
  have z : ∀ (k : ℕ) (e : j.1 + 1 = k), (e ▸ (0 : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) : D.what₂.Mt (D.nd.mu i) k) = 0 := by
    intro k e
    subst e
    rfl
  rw [z]
  exact zero_mem _

example {M : MtFam D} {rep} (A : Agree X M rep) {μ} (hμ : Used0 D μ) (j : Fin D.R.m) (x) (h k) :
    (M μ (j.1 + 1) (by omega) (by omega)).real x (h * k) =
      A.eW μ hμ j (X.fn hμ j x ((A.PV j).ψ ((A.a j)⁻¹ * h) * (A.PV j).ψ k)) := by
  rw [A.real μ hμ, ← mul_assoc, map_mul]

end GlobalTheory.NJoin

end
