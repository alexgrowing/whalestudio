import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def IsRoot1 (z : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ z ^ n = 1

def UnitOff (N : ℕ) (u : ℂ) : Prop :=
  u ≠ 0 ∧ ∃ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ n * u) ∧ IsIntegral ℤ ((N : ℂ) ^ n * u⁻¹)

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def ConjTup (τ : ℂ ≃+* ℂ) (t t' : T0) : Prop :=
  R.Q t' = R.Q t ∧ ∀ x, ((R.xi t' x : Circle) : ℂ) = τ ((R.xi t x : Circle) : ℂ)

open Classical in

def omegaFlat {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin a) (Fin b) (kP PP)) : ℂ :=
  if h : ∀ PP ∈ Q, IsUnit (topL r (y PP)).det then ∏ PP ∈ Q.attach, ((ξ PP.1 (h PP.1 PP.2).unit : ℂˣ) : ℂ) else 0

open Classical in

def IsFlatVec (i : Fin D.R.m) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∃ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum eQ (R.Q t) ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg)
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i)
      (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg
      (fun x => if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) f

def IsCentAt (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (z : GA D (Vc D i)) : Prop :=
  z ∈ Subgroup.center (GA D (Vc D i)) ∧ z ∈ GfC (Vc D i) ∧ ∃ e : AE D, IsIdemSum e Q ∧ SuppAt e (Vc D i) z

def ser (i : Fin D.R.m) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i))
    (w : (R.cV i).W) (g : GA D (Wc D i)) : ℂ :=
  thetaKO (R.ωP i t) h g (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) w))

theorem ser_vP (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (g : GA D (Wc D i)) :
    ser R i t (R.vP i t) u h w g = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) := rfl

def ConjVec (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (x x' : VsV D i ℂ) : Prop :=
  (x' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (τ : ℂ →+* ℂ) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)

def ExtC (i : Fin D.R.m) {K' : Type} [Field K'] (σ' : K' →+* ℂ) (c0 : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) : Prop :=
  ∀ (v : VsV D i K') (v' : VsV D i ℂ),
    (v' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map σ' (v : Pol K' D.what₂.Tau (Vc D i).rank) → c v' = c0 v

def ConjForm (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (t t' : T0) (y : (R.HV i t).H)
    (y' : (R.HV i t').H) : Prop :=
  ∀ h : GA D (Vc D i), ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ (R.HV i t).e y (fin _ h) = c x ∧ (R.HV i t').e y' (fin _ h) = c x'

end Any

section Core

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

structure FixBase (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) : Prop where
  core : ∀ a : T.Q.c.F, τ (a : ℂ) = (a : ℂ)
  host : ∀ (φ : D.host.E →+* ℂ) (x : D.host.E), τ (φ x) = φ x
  curve : GlobalTheory.CompRat.FixesCurve T.Q.H τ 1
  split : ∀ P : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    τ ((((R.C.mu0 i * R.C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)) =
      (((R.C.mu0 i * R.C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)
  chi : ∀ PP ∈ R.Pg, ∀ x, τ ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) = ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ)

variable {T R} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def Expands (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (Φ : GA D (Wc D i) → ℂ) {n : ℕ} (a : Fin n → ℂ)
    (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) : Prop :=
  ∀ g, Φ g = ∑ k, a k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
    O.phi (T.cE ((i : ℕ) + 1) O.s0) (f k : T.toCore.R ((i : ℕ) + 1)) g)

def ConjFun (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) : Prop :=
  (∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), Expands O κ Φ a f) ∧
    ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
      Expands O κ Φ a f → Expands O κ Φ' (fun k => ζ * τ (a k)) f

def SameCover (O : OMDat T.toCore R i Tp tup) (a b : Tp) (e : O.Cl' a ≃ O.Cl' b) : Prop :=
  (∃ cx : Rul (O.dδ a).Xo₂ (O.dδ a).c₂, O.dδ b = { O.dδ a with cδ := cx }) ∧ HEq (O.U₂ b) (O.U₂ a) ∧ HEq (O.dict₂ b) (O.dict₂ a) ∧
    O.bad b = O.bad a ∧ O.vol b = O.vol a ∧
    ∀ k, O.Lh b (e k) = O.Lh a k ∧ O.La b (e k) = O.La a k ∧ O.Nc b (e k) = O.Nc a k ∧ O.gam b (e k) = O.gam a k

end Core

end GlobalTheory.ConjTwist
