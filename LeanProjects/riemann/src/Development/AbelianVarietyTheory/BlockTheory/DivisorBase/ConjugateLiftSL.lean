import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.KernelPlaceMeanBound

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateLiftSL

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable (D) in

def OverK (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ a : D.host.K, σ (D.embE (algebraMap D.host.K D.host.E a)) = D.what₂.embLL (D.embE (algebraMap D.host.K D.host.E a))

example : OverK D D.what₂.embLL := fun _ => rfl

def LabPerm (σ : D.what₂.LL →+* ℂ) : Prop :=
  Function.Bijective (lab (D := D) σ) ∧ ∀ ρ, labE σ (lab σ ρ) = tauE D ρ

variable (D) in

def hookSum (i : Fin D.R.m) (l : D.what₂.Tau → D.what₂.Tau) : ℝ :=
  ∑ ρ, (Formalism.BasicNotions.DV.logHook ((Wc D i).sig (tauE D ρ)).1 (fun n => (aPl D i ((Wc D i).sig (tauE D ρ)).1 (l ρ) n : ℝ)) +
    Formalism.BasicNotions.DV.logHook ((Wc D i).sig (tauE D ρ)).2
      (fun n => (aMi D i ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (l ρ) n : ℝ)))

def deltaAtEmb (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : PolF D (Wc D i).rank (Vc D i).rank :=
  delta (fun ρ => ((Wc D i).sig (tauE D ρ)).1) (fun ρ => ((Wc D i).sig (tauE D ρ)).2)
    (fun ρ => aPl D i ((Wc D i).sig (tauE D ρ)).1 (lab σ ρ))
    (fun ρ => aMi D i ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (lab σ ρ))

def IsCompUnit (V : HSp D) (J : Subgroup (GA D V)) (u : GA D V → ℂ) : Prop :=
  (∀ g, ‖u g‖ = 1) ∧ (∀ γ ∈ GQ V, ∀ g, u (γ * g) = u g) ∧ (∀ k ∈ GinfC V, ∀ g, u (g * k) = u g) ∧
    ∀ k ∈ J, ∀ g, u (g * k) = u g

example (V : HSp D) (J : Subgroup (GA D V)) : IsCompUnit V J fun _ => 1 :=
  ⟨fun _ => norm_one, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

section Conj

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

def EtaAt (η' : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D η' ∧ ResEta D η' 1 ∧ (∀ ρ, HasInfExp D η' ρ (1 / 2)) ∧
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P → ∀ (k : D.host.Eˣ) (x : (AE D)ˣ),
      (x : AE D) = Formalism.L2.JoinChr.locE D e (k : D.host.E) → ∃ y : D.what₂.LL,
        D.what₂.embLL y = ((R.eta x : Circle) : ℂ) * ((Real.sqrt (FinitePlace.mk P (k : D.host.E)) : ℝ) : ℂ) ∧
        σ y = ((η' x : Circle) : ℂ) * ((Real.sqrt (FinitePlace.mk P (k : D.host.E)) : ℝ) : ℂ)

def ResAt (χ' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ PP ∈ R.Pg, ∀ u, ∃ y : D.what₂.LL,
    D.what₂.embLL y = ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) ∧ σ y = ((χ' PP u : ℂˣ) : ℂ)

def datV (χ' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ (Vc D i).rank :=
  datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg (R.Q A.μ0) (LevelP.triv _ _ _) (fun _ => χ') (R.xiR A.μ0) Frm.A

example : datV R i (R.chi ((i : ℕ) + 1)) = R.datVt i A.μ0 := rfl

def valAt (x : A.fam.amb.FL i A.μ0) (c : (A.MtCSD i A.μ0).Cl) : (A.MtCSD i A.μ0).V :=
  ((show (A.MtCSD i A.μ0).Forms from x) : (A.MtCSD i A.μ0).Cl → (A.MtCSD i A.μ0).V) c

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure ConjLift where

  mu : (AE D)ˣ →* Circle

  eta : (AE D)ˣ →* Circle

  chi : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ

  cV : CoefA (Vc D i)

  coef : (A.MtCSD i A.μ0).V →ₛₗ[σ] cV.W

  HV : HMod (Bridge.Gf (Vc D i) → cV.W)

  jV : A.fam.amb.FL i A.μ0 →ₛₗ[σ] HV.H

  om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)

  BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ

  vac : WO (Vc D i) (Wc D i) → ℂ

  vec : WO (Vc D i) (Wc D i) → ℂ

  io : LowT (R.MW i σ) →ₗ[ℂ] cV.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank

  thF : HV.H →ₗ[ℂ] MMap (R.MW i σ)

  thG : HV.H →ₗ[ℂ] (R.HW i σ).H

namespace ConjLift

variable {R i σ} (Y : ConjLift R i σ)

def pt : PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) Y.BW Y.vec

def extV : Y.HV.H →ₗ[ℂ] (GA D (Vc D i) → Y.cV.W) := Y.cV.ext ∘ₗ Y.HV.e

abbrev lev : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (datV R i Y.chi)

structure IsChr : Prop where
  mu : ChiAt R i σ Y.mu
  eta : EtaAt R σ Y.eta
  chi : ResAt R i σ Y.chi

structure IsSrc : Prop where
  cV : Y.cV.Is
  coef_li : LinearIndependent ℂ fun a => Y.coef ((A.MtCSD i A.μ0).bV a)
  coef_span : Submodule.span ℂ (Set.range fun a => Y.coef ((A.MtCSD i A.μ0).bV a)) = ⊤
  coef_pair : ∀ a b, inner ℂ (Y.coef ((A.MtCSD i A.μ0).bV a)) (Y.coef ((A.MtCSD i A.μ0).bV b)) =
    σ ((A.MtCSD i A.μ0).pair ((A.MtCSD i A.μ0).bV a) ((A.MtCSD i A.μ0).bV b))
  coef_rat : ∀ (γ : GQ (Vc D i)) (x x' : (A.MtCSD i A.μ0).V),
    (R.B.L i A.μ0).pres.coef x' = (R.cV i).coef.ρ γ ((R.B.L i A.μ0).pres.coef x) → Y.coef x' = Y.cV.coef.ρ γ (Y.coef x)
  HV : Y.HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) Y.cV.coef.ρ Y.lev.J Y.lev.χ)
    (Bridge.adInner (Bridge.ratF (Vc D i)) Y.lev.J (R.B.L i A.μ0).pres.y)
  jV : ∀ x c, Y.HV.e (Y.jV x) ((R.B.L i A.μ0).pres.y c) = Y.coef (valAt i x c)

structure IsLift : Prop where
  om : IsWeilDatumO R.ψ (Vc D i) (Wc D i) Y.mu (Y.mu * Y.eta⁻¹) Y.om
  BW : ∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (Y.BW ρ) ((Wc D i).sig (tauE D ρ)).1
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg (R.Q A.μ0) (R.xiR A.μ0) Y.vac Y.vec
  pt : ∀ P, IsThetaFunO R.ψ (Vc D i) (Wc D i) (Y.pt P)
  io : IsIoW R.θ (R.MW i σ) Y.cV Y.om Y.pt (deltaAtEmb i σ) Y.io
  thF_mem : ∀ x, Y.thF x ∈ R.Wall i σ
  thF : ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h f => thetaKO Y.om h g f) Y.pt Y.io
      (LinearMap.range Y.extV) thP ∧
    ∀ x (v : ∀ ρ, lowT (R.MW i σ) ρ),
      Y.thF x (fun ρ => v ρ) = thP (Y.extV.rangeRestrict x) (PiTensorProduct.tprod ℂ v)
  thG : ∀ x, (R.HW i σ).e (Y.thG x) = postOn _ (R.eWf i σ) (Y.thF x)

structure Is : Prop where
  chr : Y.IsChr
  src : Y.IsSrc
  lift : Y.IsLift

end ConjLift

structure IsCentralTr (z : G) : Prop where
  center : z ∈ Subgroup.center G
  lift : ∃ (k : GA D (Wc D i)) (e : AE D), IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) k ∧
    k ∈ Subgroup.center (GA D (Wc D i)) ∧ IsIdemSum e R.Pg ∧ SuppAt e (Wc D i) k ∧
    ∀ x v g, (R.HW i σ).e (R.gW i σ z x) v g = (R.HW i σ).e x v (g * k)
  unitary : ∀ x y, inner ℂ (R.gW i σ z x) (R.gW i σ z y) = inner ℂ x y
  comm_fin : ∀ g x, R.gW i σ z (R.gW i σ g x) = R.gW i σ g (R.gW i σ z x)
  comm_hecke : ∀ S : Finset (GA D (Wc D i)), (∀ γ ∈ S, γ ∈ GfC (Wc D i)) → ∀ x y,
    (R.HW i σ).e y = heckeOn (R.MW i σ) S ((R.HW i σ).e x) →
      (R.HW i σ).e (R.gW i σ z y) = heckeOn (R.MW i σ) S ((R.HW i σ).e (R.gW i σ z x))

def IsRatLift (ph : ℂ) (th : A.fam.amb.FL i A.μ0 →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  ∀ x, (R.FW i).j (sg0 D A) (th x) = ph • R.thG i A.μ0 (R.jV i A.μ0 x)

variable {R i σ} in

def ConjLift.Ident (Y : ConjLift R i σ) (th : A.fam.amb.FL i A.μ0 →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  ∃ (κ : ℂ) (z : G) (u : GA D (Wc D i) → ℂ), ‖κ‖ = 1 ∧ IsCentralTr R i σ z ∧
    IsCompUnit (Wc D i) (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) u ∧
    ∀ x v g, u g * (R.HW i σ).e ((R.FW i).j σ (th x)) v g = κ * (R.HW i σ).e (R.gW i σ z (Y.thG (Y.jV x))) v g

def GalAt (th : A.fam.amb.FL i A.μ0 →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  LabPerm (D := D) σ ∧ hookSum D i (lab σ) = hookSum D i id ∧
    (∃ Y : ConjLift R i σ, Y.Is) ∧ ∀ Y : ConjLift R i σ, Y.Is → Y.Ident th

end Conj

def GalD (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) : Prop :=
  R.Char F → ∀ t : FWTie T R κ v₀,
    (∀ (i : Fin D.R.m) (ph : ℂ), OMPins T R κ v₀ O i →
      (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph →
        (∃ th, IsRatLift R i ph th) ∧ ∀ th, IsRatLift R i ph th → ∀ σ, OverK D σ → GalAt R i σ th) ∧
    (∀ σ, OverK D σ ∨ OverK D ((starRingEnd ℂ).comp σ)) ∧
    (BarTie t → JConj R)

section Base

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def castSL {K X Z : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module ℂ Z] {s s' : K →+* ℂ} (h : s = s')
    (f : X →ₛₗ[s] Z) : X →ₛₗ[s'] Z where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by rw [← h]; exact f.map_smulₛₗ a x

include R in
theorem sign_at_base_place_eq_embedding : D.what₂.embLL = sg0 D A := (sgAt_mk _ R.hv0).symm

def base : ConjLift R i (sg0 D A) where
  mu := R.toLevCh.mu A.μ0 ((i : ℕ) + 1)
  eta := R.eta
  chi := R.chi ((i : ℕ) + 1)
  cV := R.cV i
  coef := castSL (sign_at_base_place_eq_embedding R) (R.B.L i A.μ0).pres.coef
  HV := R.HV i A.μ0
  jV := castSL (sign_at_base_place_eq_embedding R) (R.jV i A.μ0)
  om := R.ωP i A.μ0
  BW := onb (R.MW i (sg0 D A))
  vac := R.vacP i
  vec := R.vP i A.μ0
  io := R.ioP i
  thF := R.thF i A.μ0
  thG := R.thG i A.μ0

end Base

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateLiftSL
