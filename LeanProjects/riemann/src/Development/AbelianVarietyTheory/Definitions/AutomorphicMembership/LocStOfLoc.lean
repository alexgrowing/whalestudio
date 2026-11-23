import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtensionPropertyPi
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RankOneBaseWeightEqCmTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocExtANat

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.LocM

variable {D : D7} {A : Amb D} {N j : ℕ}

structure StFam (S : Sig A N j) (κ : Lv A) : Type 1 where
  st : ∀ {p : ℕ} (ct : At S κ p), Stages ct
  α : ℕ → ℕ → 𝓞 D.host.E
  hα : ∀ {p : ℕ} (ct : At S κ p), (st ct).locB.alp = α p

abbrev Ats (S : Sig A N j) (κ : Lv A) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → At S κ p

variable {S : Sig A N j} {κ : Lv A}

def Ats.Over (cts : Ats S κ) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (v : PlL D p), (cts p v).W = placeW D p v (jC p v)

def Stages.fix {p : ℕ} {ct : At S κ p} (st : Stages ct) : Stages ct := { st with mo := motTrue ct, ky := keyTrue ct }

structure LocAt (S : Sig A N j) (κ : Lv A) (p : ℕ) : Type 1 where
  loc : ModuliIntegralCharts.Loc D N j p
  ex : ModuliIntegralCharts.ExtA D loc
  locB : p.Prime → BoundaryLocalData.LocB D loc
  pbKF : ∀ {c : ℕ}, ngTrue.KF (D.R.f * N) c → loc.Sec (loc.keySh c)
  bc : CodeAt S κ → loc.Mdl

open Classical in

def bcAt {p : ℕ} (ct : At S κ p) (Z : CodeAt S κ) : ct.Mdl :=
  if h : ∃ Z', IsBCAt ct Z Z' then h.choose else ct.Xm

def primeAt (F : StFam S κ) (cts : Ats S κ) (p : ℕ) [Fact p.Prime] : LocAt S κ p :=
  haveI : Fintype (PlL D p) := finPl D p
  haveI : Nonempty (PlL D p) := plL_ne D p
  { loc := Loc.pi fun v => (F.st (cts p v)).fix.loc
    ex := ExtA.pi fun v => (F.st (cts p v)).fix.ex
    locB := fun _ => LocB.pi (fun v => (F.st (cts p v)).fix.locB) (F.α p) fun v => F.hα (cts p v)
    pbKF := fun kf v => (cts p v).pbKF kf
    bc := fun Z v => bcAt (cts p v) Z }

def fillAt (S : Sig A N j) (κ : Lv A) (p : ℕ) (hp : ¬ p.Prime) : LocAt S κ p where
  loc := (exists_loc_extA_nat D N j p).choose
  ex := (exists_loc_extA_nat D N j p).choose_spec.some
  locB h := absurd h hp
  pbKF _ := @Zero.zero _ (((exists_loc_extA_nat D N j p).choose.secAdd _).toZero)
  bc _ := (exists_loc_extA_nat D N j p).choose.Xm

def locAt (F : StFam S κ) (cts : Ats S κ) (p : ℕ) : LocAt S κ p :=
  if hp : p.Prime then @primeAt _ _ _ _ _ _ F cts p ⟨hp⟩ else fillAt S κ p hp

theorem locAt_prime (F : StFam S κ) (cts : Ats S κ) (p : ℕ) [hp : Fact p.Prime] : locAt F cts p = primeAt F cts p :=
  dif_pos hp.out

def locStOf (F : StFam S κ) (cts : Ats S κ) : LocSt D N j ngTrue where
  loc p := (locAt F cts p).loc
  ex p := (locAt F cts p).ex
  locB p := (locAt F cts p).locB
  pbKF p := (locAt F cts p).pbKF

def globStOf (F : StFam S κ) (cts : Ats S κ) : GlobSt fun p => ((locStOf F cts).loc p).Mdl where
  Xg := CodeAt S κ
  bc p := (locAt F cts p).bc
  DivG Z := CDiv Z.X
  effD B := B.Eff
  noVertD {Z} B := Z.NoVert B
  posBdD {Z} B := Z.PosBd B
  ampleOnAbelianBase Z m B := Z.AmpleHodge m B
  Met := QLB S.sys.Y κ.c κ.good
  nefFibM := QLB.NefFib
  ampleGen := QLB.AmpleGen
  limRA := QLB.LimRA

theorem locStOf_loc (F : StFam S κ) (cts : Ats S κ) (p : ℕ) [Fact p.Prime] :
    (locStOf F cts).loc p = Loc.pi fun v => (F.st (cts p v)).fix.loc :=
  congrArg LocAt.loc (locAt_prime F cts p)

end GlobalTheory.LocM
